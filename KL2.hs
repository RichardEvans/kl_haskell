module Main where

import Control.Monad
import Debug.Trace
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Tuple as Tuple
import System.Random

---------------------------------- Types --------------------------------------

data Atom = Atom Bool Char deriving (Eq, Ord)

data Rule = R Modality (Set.Set Atom) (Set.Set Atom) deriving (Eq, Ord)

data Modality = May | Must deriving (Eq, Ord)

---------------------------------- Show ---------------------------------------

instance Show Atom where
    show (Atom True c) = [c]
    show (Atom False c) = ['~', c]

instance Show Rule where show = show_rule

show_rule :: Rule -> String
show_rule (R m cs ds) = cst ++ mt ++ dst where
    cst = case Set.null cs of
        True -> "⊤"
        False -> concat (List.intersperse " ∧ " (map show csl))
    dst = case Set.null ds of
        True -> "⊥"
        False -> concat (List.intersperse " ∨ " (map show dsl))
    csl = Set.toList cs
    dsl = Set.toList ds
    mt = case m of
        May -> " ◊→ "
        Must -> " ■→ "

---------------------------------- Out Examples -------------------------------

atoms :: [(Bool, Char)] -> Set.Set Atom
atoms bcs = Set.fromList (map (\(b,c) -> Atom b c) bcs)

ex0 = ([
    R Must (atoms [(True, 'a')]) (atoms [])
    ],
    Set.empty
    )
        
ex1 = ([
    R Must (atoms [(True, 'a'), (True, 'b')]) (atoms [])
    ],
    atoms [(True, 'a')]
    )
        
ex2 = ([
    R Must (atoms [(True, 'a'), (True, 'b')]) (atoms []),
    R Must (atoms []) (atoms [(True, 'a'), (True, 'b')])
    ],
    Set.empty
    )

ex2b = ([
    R Must (atoms [(True, 'a'), (True, 'b')]) (atoms [(False, 'a'), (False, 'b')]),
    R Must (atoms []) (atoms [(True, 'a'), (True, 'b')])
    ],
    Set.empty
    )

ex3 = ([
    R Must (atoms [(True, 'a'), (True, 'b'), (True, 'c')]) (atoms [])
    ],
    atoms [(True, 'a')]
    )
        
ex4 = ([
    R Must (atoms [(True, 'a'), (True, 'b'), (True, 'c')]) (atoms [])
    ],
    atoms [(True, 'a'), (True, 'b')]
    )
        
ex5 = ([
    R Must (atoms [(True, 'a'), (True, 'b'), (True, 'c')]) (atoms []),
    R Must (atoms []) (atoms [(True, 'b'), (True, 'c')])
    ],
    atoms [(True, 'a')]
    )
        
ex6 = ([
    R Must (atoms []) (atoms [(True, 'a'), (False, 'a')])
    ],
    Set.empty
    )

ex11 = ([
    R Must (atoms [(True, 'p')]) (atoms [(True, 'q')])
    ],
    atoms [(False, 'q')]
    )

ex12 = ([
    R Must (atoms [(True, 'p'), (False, 'q')]) (atoms [])
    ],
    atoms [(True, 'p')]
    )

ex13 = ([
    R Must (atoms [(True, 'p'), (True, 'q')]) (atoms []),
    R Must (atoms [(False, 'p'), (True, 'q')]) (atoms [])
    ],
    Set.empty
    )

        
---------------------------------- out ----------------------------------------

print_out :: ([Rule], Set.Set Atom) -> IO ()
print_out (rs, as) = do
    putStrLn "Rules:"
    forM_ rs print
    putStrLn "Input: "
    print $ Set.toList as
    let xs = out rs as
    putStrLn "out:"
    forM_ xs print

complement :: Atom -> Atom
complement (Atom p a) = Atom (not p) a

is_negated :: Atom -> Bool        
is_negated (Atom p _) = not p

set_polarity :: Bool -> Atom -> Atom
set_polarity p (Atom _ a) = Atom p a

out :: [Rule] -> Set.Set Atom -> Set.Set (Set.Set Atom)
out rs a = Set.filter (satisfies_rules rs2) (cns_star rs2 a2) where
    a2 = Set.union a a'
    a' = intersections (filter f tvs)
    f tv = satisfies_rules rs tv && Set.isSubsetOf a tv
    tvs = all_tvs all_as
    as = List.nub (Set.toList a ++ all_atoms_of rs)
    all_as = List.nub (map (set_polarity True) as)
    rs' = List.nub (rs ++ Maybe.mapMaybe make_constraint rs)
    rs2 = List.nub (rs' ++ concat (map make_negation_from_constraint rs'))

make_constraint :: Rule -> Maybe Rule    
make_constraint (R May _ _) = Nothing
make_constraint (R Must bs hs) = Just (R Must (Set.union bs (Set.map complement hs)) Set.empty)

make_negation_from_constraint :: Rule -> [Rule]
make_negation_from_constraint (R Must bs hs) | Set.null hs = [R Must bs' hs' | 
    b <- Set.toList bs,
    bs' <- [Set.delete b bs],
    hs' <- [Set.singleton (complement b)]
    ]
make_negation_from_constraint _ = []

all_tvs :: [Atom] -> [Set.Set Atom]    
all_tvs [] = [Set.empty]
all_tvs (a:as) = x1 ++ x2 where
    x1 = map (Set.insert a) tvs
    x2 = map (Set.insert (set_polarity False a)) tvs
    tvs = all_tvs as

intersections :: Ord a => [Set.Set a] -> Set.Set a
intersections [] = Set.empty
intersections [x] = x
intersections (x:x':xs) = intersections (Set.intersection x x': xs)

satisfies_rules :: [Rule] -> Set.Set Atom -> Bool
satisfies_rules rs xs = all f rs' where
    f (R Must b h) | sat b = any (`Set.member` xs) h
    f _ = True
    sat y = Set.isSubsetOf y xs
    rs' = rs ++ cs
    cs = [R Must (Set.fromList [a, complement a]) (atoms []) | a <- as]
    as = List.nub (Set.toList xs ++ all_atoms_of rs)

cns_star :: [Rule] -> Set.Set Atom -> Set.Set (Set.Set Atom) 
cns_star g a = fixed_point (step g) (Set.fromList [a])

step :: [Rule] -> Set.Set (Set.Set Atom) -> Set.Set (Set.Set Atom)
step g as = Set.union as (step_1 g as)

step_1 :: [Rule] -> Set.Set (Set.Set Atom) -> Set.Set (Set.Set Atom)
step_1 rs xss = Set.unions $ map f (Set.toList xss) where
    f xs = Set.unions $ map (g xs) rs
    g xs r@(R _ bs ds) = case Set.isSubsetOf bs xs of
        False -> Set.empty
        True -> Set.fromList $ map (\d -> Set.insert d xs) (Set.toList ds)
 
subset :: Eq a => [a] -> [a] -> Bool    
subset xs ys = all (`elem` ys) xs

subsets :: [a] -> [[a]]
subsets []  = [[]]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)

all_atoms_of :: [Rule] -> [Atom]    
all_atoms_of rs = List.sort $ List.nub $ concat (map all_atoms_of_rule rs)

all_atoms_of_rule :: Rule -> [Atom]
all_atoms_of_rule (R _ a h) = concat (map f xs) where
    xs = Set.toList a ++ Set.toList h
    f a = [a, complement a]

fixed_point :: Eq a => (a->a) -> a -> a
fixed_point f a = 
    if f a == a then a
    else fixed_point f (f a)

---------------------------------- sampling -----------------------------------

total_alphabet :: [Atom]
total_alphabet = [Atom pol a | a <- ['p', 'q', 'r', 'x', 'y', 'z'], 
                                pol <- [True, False]]

print_random_rules :: IO ()
print_random_rules = do
    r <- newStdGen
    let (num_letters, r2) = pick [2..5] r
    let alphabet = take num_letters total_alphabet
    let (rs, _) = sample_rules 10 5 alphabet r2
    forM_ rs print 

sample_entailments :: IO ()
sample_entailments = do
    sample_entailment
    sample_entailments

sample_entailment :: IO ([Rule], Rule)
sample_entailment = do
    r <- newStdGen
    let (rules, rule) = make_entailment r
    forM_ rules print
    putStrLn "entails"
    print rule
    putStrLn "-----------------------"
    case weak_entails rules rule of
        False -> error "But does not strongly entail"
        True -> return ()
    return (rules, rule)

weak_entails :: [Rule] -> Rule -> Bool
weak_entails rs r = weak_equiv rs (r: rs)

weak_equiv :: [Rule] -> [Rule] -> Bool
weak_equiv rs rs' = all (\a -> out rs a == out rs' a) ss where
    ss = map Set.fromList (subsets all_as)
    all_as = all_atoms_of (rs ++ rs')

print_entails :: ([Rule], Rule) -> IO ()
print_entails (rs, r) = do
    case rs of
        [] -> putStrLn "{}"
        _ -> forM_ rs print
    case rs `weak_entails` r of
        True -> putStrLn "⊧"
        False -> putStrLn "⊭"
    print r

make_entailment :: RandomGen r => r -> ([Rule], Rule)
make_entailment r = case (rules `weak_entails` rule) of
    True -> case any (\rs -> rs `weak_entails` rule && rs /= rules) srs of
        False -> (rules, rule)
        True -> make_entailment r5
    False -> make_entailment r5
    where
        (k, r2) = pick [2..5] r
        as = take k total_alphabet
        (n, r3) = pick [2..4] r2
        (rules, r4) = sample_rules n k as r3
        ([rule], r5) = sample_rules 1 k as r4
        srs = filter (\s -> length s <= 2) (subsets rules)

sample_rules :: RandomGen r => Int -> Int -> [Atom] -> r -> ([Rule], r)
sample_rules n k as r = sample_rules2 n k as r []

sample_rules2 :: RandomGen r => Int -> Int -> [Atom] -> r -> [Rule] -> ([Rule], r)
sample_rules2 0 _ _ r acc = (acc, r)
sample_rules2 n k as r acc = sample_rules2 (n-1) k as r4 (rule:acc) where
    (n_bs, r2) = pick [0..k'] r
    (n_hs, r3) = pick [0..k'] r2
    k' = min k (length as)
    (rule, r4) = sample_rule n_bs n_hs as r3

sample_rule :: RandomGen r => Int -> Int -> [Atom] -> r -> (Rule, r)
sample_rule n_bs n_hs alphabet _ | n_bs > length alphabet = error "Alphabet too small"
sample_rule n_bs n_hs alphabet _ | n_hs > length alphabet = error "Alphabet too small"
sample_rule n_bs n_hs alphabet r = sample_rule2 n_bs n_hs alphabet m r2 where
    (m, r2) = pick [May, Must] r

sample_rule2 :: RandomGen r => Int -> Int -> [Atom] -> Modality -> r -> (Rule, r)
sample_rule2 n_bs n_hs alphabet m r = (R m b' h', r3) where
    (b, _, r2) = take_n alphabet n_bs r
    (h, _, r3) = take_n alphabet n_hs r2
    b' = Set.fromList b
    h' = Set.fromList h

pick :: RandomGen r => [a] -> r -> (a, r)
pick [] _ = error "pick wrongly given empty list"
pick as r =
    let indices = (0, length as-1)
        (i, r') = randomR indices r
    in  (as !! i, r')

pick_n :: RandomGen r => Int -> [a] -> r -> ([a], r)   
pick_n n xs r = pick_n2 n xs r []

pick_n2 :: RandomGen r => Int -> [a] -> r -> [a] -> ([a], r)   
pick_n2 0 _ r acc = (acc, r)
pick_n2 n xs r acc = pick_n2 (n-1) xs r2 (x:acc) where
    (x, r2) = pick xs r

take_n :: (Show a, RandomGen r) => [a] -> Int -> r -> ([a], [a], r)
take_n as n _ | n > length as = error $ "Invalid args to take_n: " ++ show as ++ "; " ++ show n
take_n as n r = take_n2 as n r []

take_n2 :: RandomGen r => [a] -> Int -> r -> [a] -> ([a], [a], r)
take_n2 as n r acc | length acc == n = (acc, as, r)
take_n2 as n r acc | otherwise = take_n2 as' n r' (a:acc) where
  (a, as', r') = pick_take as r

pick_take :: RandomGen r => [a] -> r -> (a, [a], r)
pick_take [] _ = error "pick_take wrongly given empty list"
pick_take as r = 
    let indices = (0, length as-1)
        (i, r') = randomR indices r
    in  (as !! i, take i as ++ drop (i+1) as, r')

---------------------------------- Entails Examples ---------------------------

good_ent1 = ([
    R Must (atoms [(True, 'p')]) (atoms [(True, 'q')])
    ], 
    R Must (atoms [(True, 'p')]) (atoms [(True, 'q'), (False, 'q')])
    )

good_ent2 = ([
    R Must (atoms [(True, 'p')]) (atoms [(False, 'q')])
    ], 
    R Must (atoms [(True, 'p'), (True, 'q')]) (atoms [])
    )

good_ent3 = ([
    R Must (atoms [(True, 'p'), (True, 'q')]) (atoms [])
    ], 
    R Must (atoms [(True, 'p')]) (atoms [(False, 'q')])
    )

good_ent4 = ([
    R Must (atoms [(True, 'p')]) (atoms [(True, 'q')])
    ], 
    R May (atoms [(False, 'q')]) (atoms [(False, 'p')])
    )

good_ent5 = ([
    R Must (atoms [(False, 'p')]) (atoms [])
    ], 
    R May (atoms []) (atoms [(True, 'p')])
    )

good_ent6 = ([
    R Must (atoms [(False, 'p')]) (atoms [(True, 'p')]),
    R May (atoms []) (atoms [(False, 'p')])
    ], 
    R May (atoms []) (atoms [(True, 'p'), (False, 'p')])
    )

good_ent7 = ([
    R Must (atoms [(False, 'q')]) (atoms [(False, 'p')])
    ], 
    R Must (atoms [(True, 'p')]) (atoms [(True, 'q')])
    )

good_ent8 = ([
    R Must (atoms [(True, 'p')]) (atoms [(True, 'q')])
    ], 
    R Must (atoms [(True, 'p'), (False, 'q')]) (atoms [])
    )

good_ent9 = ([
    R Must (atoms [(True, 'p'), (False, 'q')]) (atoms [])
    ], 
    R Must (atoms [(True, 'p')]) (atoms [(True, 'q')])
    )

good_ent10 = ([
    R Must (atoms []) (atoms [(True, 'p')])
    ], 
    R Must (atoms [(False, 'p')]) (atoms [])
    )

good_ent11 = ([
    R Must (atoms [(True, 'p'), (True, 'q')]) (atoms []),
    R Must (atoms [(False, 'p'), (True, 'q')]) (atoms [])
        ],
    R Must (atoms []) (atoms [(False, 'q')])
    )

good_ent12 = ([
    R Must (atoms []) (atoms [(False, 'a'), (False, 'b')])     
    ],
    R Must (atoms [(True, 'a'), (True, 'b')]) (atoms [])
    )

good_ent14 = ([
    R Must (atoms [(True, 'p')]) (atoms [(False, 'p')]),
    R Must (atoms [(False, 'p')]) (atoms [(True, 'p')])
    ],
    R Must (atoms []) (atoms [])
    )

bad_ent1 = ([], 
    R Must (atoms []) (atoms [(True, 'a'), (False, 'a')])
    )

bad_ent2 = ([
    R Must (atoms [(True, 'a'), (True, 'b')]) (atoms [])
    ],
    R Must (atoms []) (atoms [(False, 'a'), (False, 'b')]) 
    )

test_ent = ([
    R Must (atoms []) (atoms [(False, 'p'), (True, 'q')]) 
    ], 
    R Must (atoms [(True, 'p')]) (atoms [(True, 'q')])
    )

entailments = [good_ent1, good_ent2, good_ent3, good_ent4, good_ent5, good_ent6, good_ent7, good_ent8, good_ent9, good_ent10, good_ent11, good_ent12]

bad_entailments = [bad_ent1, bad_ent2]

---------------------------------- inference ----------------------------------

type Inference = (String, Set.Set Rule -> Set.Set Atom -> Set.Set Rule)

infer_step :: Set.Set Rule -> Set.Set Atom -> [(String, Set.Set Rule)]
infer_step rs as = map g inference_rules where
    g (name, f) = (name, Set.difference (f rs as) rs)

infer :: Set.Set Atom -> Set.Set Rule -> Set.Set Rule
infer as rs = fixed_point (infer1 as) rs

infer1 :: Set.Set Atom -> Set.Set Rule -> Set.Set Rule
infer1 as rs = Set.unions (map g inference_rules) where
    g (_, f) = Set.union (f rs as) rs

infer_io :: Set.Set Atom -> Set.Set Rule -> IO (Set.Set Rule)
infer_io as rs = do
    let g (name, f) = (name, Set.difference (f rs as) rs)
    let infs = map g inference_rules
    forM_ infs $ \(name, rs') -> do
        case Set.null rs' of
            True -> return ()
            False -> do
                putStrLn $ "Using " ++ name
                let rsl = Set.toList rs'
                forM_ rsl print
    putStrLn "---"
    let rs' = Set.unions (map snd infs)
    let rs2 = Set.union rs rs'
    case rs == rs2 of
        True -> return rs
        False -> infer_io as rs2    

test_soundness :: Int -> IO ()
test_soundness n = forM_ [1..n] $ \i -> do
    putStrLn $ "Soundness example " ++ show i
    r <- newStdGen
    let (k, r2) = pick [2..4] r -- pick [2..5] r
    let as = take k total_alphabet
    let (n, r3) = pick [2..4] r2
    let (rs, _) = sample_rules n k as r3
    putStrLn "Sampled rules:"
    forM_ rs print
    check_soundness rs

check_soundness :: [Rule] -> IO ()    
check_soundness rs = do
    let as = all_atoms_of rs
    let rss = Set.fromList rs
    rs' <- infer_io (Set.fromList as) rss
    let rsl = Set.toList (Set.difference rs' rss)
    forM_ rsl $ \r -> case rs `weak_entails` r of
        False -> error $ "Invalid rule: " ++ show r
        True -> return ()

test_completeness :: Int -> IO ()
test_completeness n = forM_ [1..n] $ \i -> do
    putStrLn $ "Completeness example " ++ show i
    (rs, r) <- sample_entailment
    putStrLn "Sampled entailment."
    putStrLn "Rules:"
    forM_ rs print
    putStrLn "Entails:"
    print r
    putStrLn "---"
    check_completeness (rs, r)

check_entailments :: IO ()
check_entailments = do
    forM_ entailments $ \(rs,r) -> do
        case rs of
            [] -> putStrLn "{}"
            _ -> forM_ rs print
        putStrLn "⊧"
        print r
        case rs `weak_entails` r of
            True -> putStrLn "OK"
            False -> error "Entailment false negative"
    forM_ bad_entailments $ \(rs,r) -> do
        case rs of
            [] -> putStrLn "{}"
            _ -> forM_ rs print
        putStrLn "⊭"
        print r
        case rs `weak_entails` r of
            False -> putStrLn "OK"
            True -> error "Entailment false positive"

test_entailments :: IO ()
test_entailments = forM_ entailments $ \(rs, r) -> do
    putStrLn "==="
    case rs of
        [] -> putStrLn "{}"
        _ -> forM_ rs print
    putStrLn "⊧"
    print r
    case rs `weak_entails` r of
        True -> check_completeness (rs, r)
        False -> error "Unexpected entailment failure"

check_completeness :: ([Rule], Rule) -> IO ()    
check_completeness (rs, r) = do
    let as = Set.fromList (all_atoms_of (r : rs))
    infs <- infer_io as (Set.fromList rs)
    case Set.member r infs of
        True -> putStrLn "OK"
        False -> error "No entailment found"

inference_rules :: [Inference]
inference_rules = [
    ("MAY-AXIOM", infer_may_axiom), 
    ("MAY-SI", infer_may_si), 
    ("MAY-WO", infer_may_wo),
    ("MAY-MUST", infer_may_must),
    ("MAY-FALSUM-MUST", infer_may_falsum_must),
    ("MAY-UNION", infer_may_union),
    ("MAY-TRANS", infer_may_trans),
    ("MUST-ID", infer_must_id),
    ("MUST-SI", infer_must_si),
    ("MUST-QUOD-LIBET", infer_must_quod_libet),
    ("MUST-MAY-UNION", infer_must_may_union),
    ("MUST-TRANS", infer_must_trans),
    ("NOT-LEFT", infer_not_left),
    ("NOT-RIGHT", infer_not_right)
    ]

infer_may_axiom :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_may_axiom _ _ = Set.singleton (R May Set.empty Set.empty)

infer_may_id :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_may_id _ as = Set.fromList [R May (Set.singleton a) (Set.singleton a) | a <- Set.toList as]

infer_may_si :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_may_si rs as = Set.fromList [R May (Set.union bs (Set.fromList bs')) hs |
    R May bs hs <- Set.toList rs, 
    bs' <- subsets (Set.toList as),
    not (Set.isSubsetOf (Set.fromList bs') bs)
    ]

infer_may_wo :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_may_wo rs as = Set.fromList [R May bs (Set.fromList hs') |
    R May bs hs <- Set.toList rs, 
    hs' <- subsets (Set.toList hs)
    ]

infer_may_must :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_may_must rs as = Set.fromList [R May bs hs |
    R Must bs hs <- Set.toList rs
    ]

infer_may_falsum_must :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_may_falsum_must rs _ = Set.fromList [R May (Set.delete b as) (Set.singleton b) | 
    R Must as bs <- Set.toList rs,
    Set.null bs,
    b <- Set.toList as
    ]

infer_may_union :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_may_union rs as = Set.fromList [R May bs (Set.union hs hs') |
    R May bs hs <- Set.toList rs,
    R May bs' hs' <- Set.toList rs,
    bs == bs'
    ]

infer_must_id :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_must_id _ as = Set.fromList [R Must (Set.singleton a) (Set.singleton a) | a <- Set.toList as]

infer_must_si :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_must_si rs as = Set.fromList [R Must (Set.union bs (Set.fromList bs')) hs |
    R Must bs hs <- Set.toList rs, 
    bs' <- subsets (Set.toList as),
    not (Set.isSubsetOf (Set.fromList bs') bs)
    ]

infer_must_union :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_must_union rs as = Set.fromList [R Must bs (Set.union hs hs') |
    R Must bs hs <- Set.toList rs,
    R Must bs' hs' <- Set.toList rs,
    bs == bs'
    ]

infer_must_intersect :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_must_intersect rs as = Set.fromList [R Must bs (Set.intersection hs hs') |
    R Must bs hs <- Set.toList rs,
    R Must bs' hs' <- Set.toList rs,
    bs == bs'
    ]

infer_must_may_union :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_must_may_union rs as = Set.fromList [R Must bs (Set.union hs hs') |
    R Must bs hs <- Set.toList rs,
    R May bs' hs' <- Set.toList rs,
    bs == bs'
    ]

infer_must_quod_libet :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_must_quod_libet rs as = Set.fromList [R Must bs (Set.fromList hs) | 
    R Must bs h <- Set.toList rs,
    Set.null h,
    hs <- subsets (Set.toList as),
    not (null hs)
    ]

infer_must_trans :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_must_trans rs as = Set.fromList [R Must bs (Set.fromList hs2) | 
    R Must bs hs <- Set.toList rs,
    hs2 <- subsets (Set.toList as),
    must_trans_check rs bs hs (Set.fromList hs2)
    ]

must_trans_check :: Set.Set Rule -> Set.Set Atom -> Set.Set Atom -> Set.Set Atom -> Bool    
must_trans_check rs bs hs hs2 = all f (Set.toList hs) where
    f h = (R Must (Set.insert h bs) hs2) `Set.member` rs

infer_may_trans :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_may_trans rs atoms = Set.fromList [R May as (Set.fromList cs) | 
    R May as bs <- Set.toList rs,
    not (Set.null bs),
    cs <- subsets (Set.toList atoms),
    may_trans_check rs as bs (Set.fromList cs)
    ]

may_trans_check :: Set.Set Rule -> Set.Set Atom -> Set.Set Atom -> Set.Set Atom -> Bool    
may_trans_check rs as bs cs = all f (Set.toList bs) where
    f b = (R May (Set.insert b as) cs) `Set.member` rs && all (g b) (Set.toList cs)
    g b c = (R Must (Set.insert c as) (Set.singleton b)) `Set.member` rs 

infer_must_or :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_must_or rs as = Set.fromList [R Must bs (Set.insert h hs) | 
    R Must bs hs <- Set.toList rs,
    h <- Set.toList as,
    R Must bs' hs' <- Set.toList rs,
    Set.null hs',
    bs' == Set.insert h bs
    ]

infer_may_or :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_may_or rs as = Set.fromList [R May bs (Set.insert h hs) | 
    R May bs hs <- Set.toList rs,
    h <- Set.toList as,
    R Must bs' hs' <- Set.toList rs,
    Set.null hs',
    bs' == Set.insert h bs
    ]

infer_not_right :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_not_right rs as = Set.fromList [R Must bs' (Set.singleton (complement b)) |
    R Must bs hs <- Set.toList rs,
    Set.null hs,
    b <- Set.toList bs,
    bs' <- [Set.delete b bs]
    ]

infer_not_left :: Set.Set Rule -> Set.Set Atom -> Set.Set Rule
infer_not_left _ as = Set.fromList [R Must (Set.fromList [a, complement a]) (Set.empty) | a <- Set.toList as]

---------------------------------- main --------------------------------------

main :: IO ()
main = do
    check_entailments
    test_entailments
    test_soundness 10000
    test_completeness 10000



