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

data Atom = Atom Char deriving (Eq, Ord)

data Rule = R Modality (Set.Set Atom) (Set.Set Atom) deriving (Eq, Ord)

data Modality = May | Must deriving (Eq, Ord)

---------------------------------- Show ---------------------------------------

instance Show Atom where
    show (Atom c) = [c]

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

---------------------------------- Examples -----------------------------------

atoms1 :: Char -> Set.Set Atom
atoms1 a = Set.fromList [Atom a]

atoms2 :: Char -> Char -> Set.Set Atom
atoms2 a b = Set.fromList [Atom a, Atom b]

atoms3 :: Char -> Char -> Char -> Set.Set Atom
atoms3 a b c = Set.fromList [Atom a, Atom b, Atom c]

ex1 = ([
    R Must (atoms1 'p') (atoms2 'q' 'r'),
    R Must (atoms1 'q') Set.empty
    ],
    Set.fromList [Atom 'p']
    )

ex2 = ([
    R Must (atoms1 'p') (atoms2 'q' 'r'),
    R Must (atoms1 'q') (atoms1 's'),
    R Must (atoms1 'r') (atoms1 's')
    ],
    Set.fromList [Atom 'p']
    )

ex3 = ([
    R May (atoms1 'p') (atoms1 'q'),
    R May (atoms1 'p') (atoms1 'r'),
    R Must (atoms2 'q' 'r') Set.empty
    ],
    Set.fromList [Atom 'p']
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
    let ys = out_m rs as
    putStrLn "out_m:"
    forM_ ys print
    case xs == ys of
        True -> return ()
        False -> error "ERROR: discrepancy between out and out_m!"

out :: [Rule] -> Set.Set Atom -> Set.Set (Set.Set Atom)
out rs a = Set.filter (satisfies_rules rs) (cns_star rs a)

satisfies_rules :: [Rule] -> Set.Set Atom -> Bool
satisfies_rules rs xs = all f rs where
    f (R Must b h) | sat b = any (`Set.member` xs) h
    f _ = True
    sat y = Set.isSubsetOf y xs

cns_star :: [Rule] -> Set.Set Atom -> Set.Set (Set.Set Atom) 
cns_star g a = fixed_point (step g) (Set.fromList [a])

step :: [Rule] -> Set.Set (Set.Set Atom) -> Set.Set (Set.Set Atom)
step g as = Set.union as (step_1 g as)

step_1 :: [Rule] -> Set.Set (Set.Set Atom) -> Set.Set (Set.Set Atom)
step_1 rs xss = Set.unions $ map f (Set.toList xss) where
    f xs = Set.unions $ map (g xs) rs
    g xs r@(R _ b ds) = case Set.isSubsetOf b xs of
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
all_atoms_of_rule (R _ a h) = Set.toList a ++ Set.toList h

fixed_point :: Eq a => (a->a) -> a -> a
fixed_point f a = 
    if f a == a then a
    else fixed_point f (f a)

---------------------------------- sampling -----------------------------------

total_alphabet :: [Atom]
total_alphabet = [Atom a | a <- ['p', 'q', 'r', 'x', 'y', 'z']]

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
    case strong_entails rules rule of
        False -> error "But does not strongly entail"
        True -> return ()
    return (rules, rule)

check_monotonicity :: Int -> IO ()
check_monotonicity n = forM_ [1..n] $ \i -> do
    putStrLn $ "Example " ++ show i
    r <- newStdGen
    let (rules, rule) = make_entailment r
    r' <- newStdGen
    let (k, r2) = pick [2..5] r'
    let as = take k total_alphabet
    let ([new_rule], _) = sample_rules 1 k as r2
    case strong_entails (new_rule:rules) rule of
        True -> putStrLn "OK"
        False -> do
            forM_ rules print
            putStrLn "entails"
            print rule
            putStrLn "but not with"
            print new_rule
            error "Non-monotonic example found"

sample_equivs :: IO ()
sample_equivs = do
    sample_equiv
    sample_equivs

sample_equiv :: IO ([Rule], [Rule])
sample_equiv = do
    r <- newStdGen
    let (k, r2) = pick [2..5] r
    let as = take k total_alphabet
    let (n, r3) = pick [2..4] r2
    let (rs, r4) = sample_rules n k as r3
    let (rs', _) = sample_rules n k as r4
    case weak_equiv rs rs' of
        False -> sample_equiv
        True -> do
            putStrLn "Weak equivalence found."
            putStrLn "rs:"
            forM_ rs print
            putStrLn "rs':"
            forM_ rs' print
            case strong_equiv rs rs' of
                True -> return (rs, rs')
                False -> error "But they are *not* strongly equivalent..."

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

verify_out_equals_out_m :: Int -> IO ()
verify_out_equals_out_m n = forM_ [1..n] $ \_ -> do
    r <- newStdGen
    let (k, r2) = pick [2..5] r
    let as = take k total_alphabet
    let (n, r3) = pick [2..4] r2
    let (rules, r4) = sample_rules n k as r3
    let ss = subsets as
    let (as, _) = pick ss r4
    putStrLn "Rules:"
    forM_ rules print
    putStrLn "Input:"
    print as
    let xs = out rules (Set.fromList as)
    let ys = out_m rules (Set.fromList as)
    case xs == ys of
        True -> do
            forM_ xs print
            putStrLn "OK"
            putStrLn "---"
        False -> do
            putStrLn "ERROR!"
            putStrLn "out:"
            forM_ xs print
            putStrLn "out_m:"
            forM_ ys print
            error "ERROR! Discrepancy found"

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

---------------------------------- HT -----------------------------------------

data Formula =  Bot |
                Top |
                A Atom | 
                Conj Formula Formula | 
                Disj Formula Formula | 
                Imp Formula Formula
                deriving (Eq, Ord)

data World = Here | There deriving (Eq, Ord)

data Model = Model { 
    here :: Set.Set Atom,
    there :: Set.Set Atom,
    world :: World
    } deriving (Eq, Ord)

instance Show Formula where
    show Bot = "⊥"
    show Top = "⊤"
    show (A a) = show a
    show (Conj a b) = "(" ++ show a ++ " ∧ " ++ show b ++ ")"
    show (Disj a b) = "(" ++ show a ++ " ∨ " ++ show b ++ ")"
    show (Imp a b) = "(" ++ show a ++ " → " ++ show b ++ ")"

instance Show World where
    show Here = "H"
    show There = "T"

instance Show Model where
    show m = unlines [
        "T: " ++ concat (List.intersperse ", " (map show (Set.toList (there m)))),
        "H: " ++ concat (List.intersperse ", " (map show (Set.toList (here m)))),
        "world: " ++ show (world m)
        ]

sat :: Model -> Formula -> Bool
sat _ Bot = False
sat _ Top = True
sat m (A a) = Set.member a (world_atoms m)
sat m (Conj a b) = sat m a && sat m b
sat m (Disj a b) = sat m a || sat m b
sat m (Imp a b) = all f (all_geq m) where
    f w = let m' = m { world = w } in not (sat m' a) || sat m' b

all_geq :: Model -> [World]
all_geq m = case world m of
    Here -> [Here, There]
    There -> [There]

world_atoms :: Model -> Set.Set Atom
world_atoms m = case world m of
    Here -> here m
    There -> there m

---------------------------------- Models -------------------------------------

atoms :: Formula -> Set.Set Atom
atoms Bot = Set.empty
atoms Top = Set.empty
atoms (A a) = Set.singleton a
atoms (Conj a b) = Set.union (atoms a) (atoms b) 
atoms (Disj a b) = Set.union (atoms a) (atoms b) 
atoms (Imp a b) = Set.union (atoms a) (atoms b) 

all_atoms :: [Formula] -> Set.Set Atom
all_atoms fs = Set.unions (map atoms fs)

all_possible_models :: [Atom] -> [Model]
all_possible_models as = [ model_from_pair h t |
    h <- subsets as,
    t <- subsets as,
    is_subset h t
    ]

is_subset :: Eq a => [a] -> [a] -> Bool
is_subset xs ys = all (`elem` ys) xs

model_from_pair :: [Atom] -> [Atom] -> Model
model_from_pair h t = Model { 
    here = Set.fromList h, 
    there = Set.fromList t, 
    world = Here 
}

equilibrium_models :: [Formula] -> [Model]
equilibrium_models fs = filter (is_equilibrium ms) ms where
    ms = models fs as
    as = Set.toList (all_atoms fs)

models :: [Formula] -> [Atom] -> [Model]
models fs as = List.sort $ filter f (all_possible_models as) where
    f m = all (sat m) fs
    
is_equilibrium :: [Model] -> Model -> Bool
is_equilibrium ms m = here m == there m && not (any sub_model ms) where
    sub_model m' =  here m' /= here m &&
                    Set.isSubsetOf (here m') (here m) && 
                    there m' == there m

eq :: [Formula] -> Set.Set (Set.Set Atom)
eq fs = Set.fromList (map here (equilibrium_models fs))        

fs1 = [ Disj (A (Atom 'p')) (A (Atom 'q')) ]

fs2 = [ Imp (Imp (A (Atom 'p')) Bot) (A (Atom 'q')), 
        Imp (Imp (A (Atom 'q')) Bot) (A (Atom 'p'))]

fs3 = [ Disj (A (Atom 'p')) (A (Atom 'q')), Imp (A (Atom 'p')) Bot ]

---------------------------------- Translate ----------------------------------

neg :: Formula -> Formula
neg f = Imp f Bot

tr :: Rule -> [Formula]
tr (R Must as bs) = c : tr (R May as bs) where
    c = neg (conj2 af (conj_list neg_bs))
    af = conj_list (map A (Set.toList as))
    neg_bs = [neg (A b) | b <- Set.toList bs]
tr (R May as bs) = imps where
    imps = [Imp (conj2 (conj_list (map A asl)) (neg (neg (A b)))) (A b) | 
            b <- bsl]
    asl = Set.toList as
    bsl = Set.toList bs

tr2 :: [Rule] -> [Formula]
tr2 rs = concat (map tr rs)    

conj_list :: [Formula] -> Formula
conj_list [] = Top
conj_list (f : fs) = conj2 f (conj_list fs)

conj2 :: Formula -> Formula -> Formula
conj2 Top f = f
conj2 f Top = f
conj2 a b = Conj a b

---------------------------------- out_m --------------------------------------

out_m :: [Rule] -> Set.Set Atom -> Set.Set (Set.Set Atom)
out_m rs as = eq (map A (Set.toList as) ++ concat (map tr rs))

---------------------------------- entails ------------------------------------

weak_entails :: [Rule] -> Rule -> Bool
weak_entails rs r = weak_equiv rs (r: rs)

strong_entails :: [Rule] -> Rule -> Bool
strong_entails rs r = strong_equiv rs (r:rs)

weak_equiv :: [Rule] -> [Rule] -> Bool
weak_equiv rs rs' = all (\a -> out rs a == out rs' a) ss where
    ss = map Set.fromList (subsets all_as)
    all_as = all_atoms_of (rs ++ rs')

strong_equiv :: [Rule] -> [Rule] -> Bool
strong_equiv rs rs' = models (tr2 rs) as == models (tr2 rs') as where
    as = List.nub (all_atoms_of rs ++ all_atoms_of rs')

---------------------------------- examples -----------------------------------

ent1 = ([
    R May (atoms1 'p') (atoms2 'q' 'r')
    ],
    R May (atoms2 'p' 'w') (atoms1 'q')
    )
        
ent2 = ([
    R Must (atoms1 'p') Set.empty
    ],
    R May (atoms2 'p' 'q') (atoms1 'r')
    )
        
ent3 = ([
    R May (atoms1 'p') (atoms1 'q'),
    R May (atoms1 'r') (atoms1 's')
    ],
    R May (atoms2 'p' 'r') (atoms2 'q' 's')
    )

ent4 = ([
    R Must (atoms1 'p') (atoms1 'q'),
    R Must (atoms1 'q') (atoms1 'r')
    ],
    R Must (atoms1 'p') (atoms1 'r')
    )

ent5 = ([
    R Must (atoms2 'p' 'q') Set.empty
    ],
    R Must (atoms1 'p') (atoms2 'p' 'q')
    )

ent6 = ([
    R Must Set.empty (atoms2 'q' 'r'),
    R Must (atoms1 'p') (atoms1 'r'),
    R May (atoms2 'q' 'r') (atoms2 'p' 'r')
    ],
    R May (atoms1 'p') (atoms2 'p' 'q')
    )

ent7 = ([
    R Must (atoms1 'p') Set.empty,
    R May Set.empty (atoms1 'q')
    ],
    R May Set.empty (atoms2 'p' 'q')
    )

ent8 = ([
    R May Set.empty (atoms1 'p'),
    R Must (atoms1 'q') (atoms1 'p'),
    R May (atoms1 'p') (atoms1 'q')
    ],
    R May Set.empty (atoms1 'q')
    )

ent9 = ([
    R May (atoms1 'p') (atoms2 'q' 'r'),
    R May (atoms1 'q') (atoms1 's'),
    R May (atoms1 'r') (atoms1 's'),
    R Must (atoms1 's') (atoms1 'q'),
    R Must (atoms1 's') (atoms1 'r')
    ],
    R May (atoms1 'p') (atoms1 's')
    )

ent10 = ([
    R Must (atoms1 'p') Set.empty
    ],
    R May Set.empty (atoms1 'p')
    )

ent11 = ([
    ],
    R May Set.empty Set.empty
    )

ent12 = ([
    R May (atoms1 'p') (atoms2 'q' 'r'),
    R May (atoms2 'p' 'q') (atoms2 'x' 'y'),
    R May (atoms2 'p' 'r') (atoms2 'x' 'y'),
    R Must (atoms2 'p' 'x') (atoms1 'q'),
    R Must (atoms2 'p' 'y') (atoms1 'r')
    ],
    R May (atoms1 'p') (atoms2 'x' 'y')
    )

ent13 = ([
    R Must (atoms1 'p') (atoms1 'q')
    ],
    R Must (atoms1 'p') (atoms2 'p' 'q')
    )

ent14 = ([
    R May (atoms1 'p') (atoms1 'q')
    ],
    R May (atoms1 'p') (atoms2 'p' 'q')
    )

ent15 = ([
    R Must Set.empty (atoms1 'p')
    ],
    R Must (atoms1 'q') (atoms2 'p' 'q')
    )

ent16 = ([
    R Must (atoms1 'p') (atoms2 'p' 'q')
    ],
    R May Set.empty (atoms1 'q')
    )

ent17 = ([
    R Must (atoms1 'p') (atoms2 'p' 'q')
    ],
    R May (atoms1 'p') (atoms1 'q')
    )

ent18 = ([
    R May (atoms1 'p') (atoms2 'p' 'q')
    ],
    R May (atoms1 'p') (atoms1 'q')
    )

ent19 = ([
    R Must (atoms1 'p') (atoms1 'q'),
    R Must (atoms1 'p') (atoms1 'r'),
    R Must (atoms2 'q' 'r') (atoms1 's')
    ],
    R Must (atoms1 'p') (atoms1 's')
    )

ent20 = ([
    R Must (atoms1 'p') (atoms1 'q'),
    R Must (atoms1 'p') (atoms1 'r')
    ],
    R Must (atoms1 'p') (atoms2 'q' 'r')
    )

entailments = [ent1, ent2, ent3, ent4, ent5, ent6, ent7, ent8, ent9, ent10, ent11, ent12, ent13]

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
    putStrLn $ "Example " ++ show i
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
    putStrLn $ "Example " ++ show i
    (rs, r) <- sample_entailment
    putStrLn "Sampled entailment."
    putStrLn "Rules:"
    forM_ rs print
    putStrLn "Entails:"
    print r
    putStrLn "---"
    check_completeness (rs, r)

test_entailments = forM_ entailments check_completeness

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
    ("MUST-TRANS", infer_must_trans)
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

---------------------------------- main ---------------------------------------

main :: IO ()
main = do
    let num_tests = 10000
    check_monotonicity num_tests
    test_soundness num_tests
    test_entailments
    test_completeness num_tests


