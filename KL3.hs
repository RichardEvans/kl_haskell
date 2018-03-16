module Main where

import Control.Monad
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Tuple as Tuple
import qualified Test.HUnit as HUnit
import Text.Read

---------------------------------- Types --------------------------------------

data Term = K String | V String deriving (Eq, Ord)

data Pred = P Bool String deriving (Eq, Ord)

data Atom = A Pred [Term] deriving (Eq, Ord)

data Rule = Must (Set.Set Atom) (Set.Set Atom) |
            May (Set.Set Atom) (Set.Set Atom)
            deriving (Eq, Ord)

data Problem = Problem [Rule] (Set.Set Atom) Bool deriving (Eq, Ord)

newtype Subs = Subs (Map.Map Term Term) deriving (Eq, Ord)

data Application = Ap Int Rule Subs Int deriving (Eq, Ord)

type Model = Maybe (Set.Set Atom)

data Node = Node Model [Application] deriving (Eq, Ord, Show)

data ChooseRule = CFinish | CBack | CInvalid | CRule Int deriving (Eq, Ord, Show)

---------------------------------- Consts -------------------------------------

empty_subs :: Subs
empty_subs = Subs (Map.empty)

equals_string :: String
equals_string = "="

null_string :: String
null_string = "null"

---------------------------------- Show ---------------------------------------

instance Show Pred where
    show (P True p) = p
    show (P False p) = "~" ++ p

instance Show Atom where
    show (A (P True p) [x, y]) | p == equals_string = show x ++ " = " ++ show y
    show (A (P False p) [x, y]) | p == equals_string = show x ++ " ≠ " ++ show y
    show (A p ts) = show p ++ "(" ++ concat (List.intersperse ", " (map show ts)) ++ ")"

instance Show Term where
    show (K k) = k
    show (V v) = v

instance Show Subs where
    show (Subs m) = "[" ++ showAssocs (Map.assocs m) ++ "]" where
        showAssocs kvps = concat (List.intersperse ", " (map showKVP kvps))
        showKVP (k,v) = show k ++ "/" ++ show v

instance Show Rule where
    show (Must as bs) =  show_conj as ++ " ■→ " ++ show_ex_qns as bs ++ show_disj bs
    show (May as bs) = show_conj as ++ " ◊→ " ++ show_ex_qns as bs ++ show_disj bs

show_conj :: Set.Set Atom -> String
show_conj as | Set.null as = "⊤"
show_conj as = concat (List.intersperse " ∧ " (map show (Set.toList as)))

show_disj :: Set.Set Atom -> String
show_disj bs | Set.null bs = "⊥"
show_disj bs = concat (List.intersperse " ∨ " (map show (Set.toList bs)))

show_ex_qns :: Set.Set Atom -> Set.Set Atom -> String
show_ex_qns as bs = t' where
    ex_vs = get_ex_vs as bs
    t = concat (List.intersperse " " (map f ex_vs))
    f e = "∃" ++ e
    t' = if null t then t else t ++ " "

get_ex_vs :: Set.Set Atom -> Set.Set Atom -> [String]
get_ex_vs as bs = ex_vs where
    v_as = List.nub (concat (map free_vars (Set.toList as)))
    v_bs = List.nub (concat (map free_vars (Set.toList bs)))
    ex_vs = v_bs List.\\ v_as

showC :: [Atom] -> String
showC [] = ""
showC [c] = show c
showC conj = concat (List.intersperse " /\\ " (map show conj)) 

instance Show Problem where
    show (Problem rs ls do_update) = concat (List.intersperse "\n" $ "Rules:" : map (\r -> "\t" ++ show r) rs ++ ("Atoms:" : map (\a -> "\t" ++ show a) (Set.toList ls)) ++ (if do_update then ["[using update_model]"] else ["[not using update_model]"]) ++ ["----"])

---------------------------------- out ----------------------------------------

out :: Int -> Problem -> Set.Set (Set.Set Atom)
out n (Problem rs a do_update) = Set.filter (valid_model rs2) (do_n n (out_step do_update rs2) (Set.fromList [a])) where
    rs' = List.nub (rs ++ Maybe.mapMaybe make_constraint rs)
    rs2 = List.nub (rs' ++ concat (map make_negation_from_constraint rs'))

valid_model :: [Rule] -> Set.Set Atom -> Bool
valid_model rs m = consistent_model m && satisfies_all rs m

satisfies_all :: [Rule] -> Set.Set Atom -> Bool
satisfies_all rs m = all (satisfies_rule m) rs && check_identities m

consistent_model :: Set.Set Atom -> Bool
consistent_model m = no_conflicts m && check_identities m

no_conflicts :: Set.Set Atom -> Bool
no_conflicts s = not (any f (Set.toList s)) where
    f (A (P True p) ts) = A (P False p) ts `Set.member` s
    f _ = False

check_identities :: Set.Set Atom -> Bool
check_identities xs = all check_identity (Set.toList xs)

check_identity :: Atom -> Bool
check_identity (A (P True p) [t1, t2]) | p == equals_string = t1 == t2
check_identity (A (P False p) [t1, t2]) | p == equals_string = t1 /= t2
check_identity _ = True

satisfies_rule :: Set.Set Atom -> Rule -> Bool
satisfies_rule m (Must as ds) = all (check_disjunction m ds) (all_subs_for_lhs m as)
satisfies_rule m (May _ _) = True

all_subs_for_lhs :: Set.Set Atom -> Set.Set Atom -> [Subs]    
all_subs_for_lhs m as = all_subs_for_conj m empty_subs as 
    
all_subs_for_conj :: Set.Set Atom -> Subs -> Set.Set Atom -> [Subs]    
all_subs_for_conj m subs as = build_subs (Set.toList $ all_atoms m) [subs] (Set.toList as)
    
check_disjunction :: Set.Set Atom -> Set.Set Atom -> Subs -> Bool
check_disjunction a ds subs = any (check_atom a subs) ds

check_atom :: Set.Set Atom -> Subs -> Atom -> Bool
check_atom m subs p = any (atoms_match (apply_subs p subs)) (all_atoms m)

atoms_match :: Atom -> Atom -> Bool
atoms_match (A (P True p) [x, y]) _ | p == equals_string = x == y
atoms_match (A (P False p) [x, y]) _ | p == equals_string = x /= y
atoms_match (A p ts) (A p' ts') = 
    p == p' && length ts == length ts' && 
    Maybe.isJust (get_subs ts ts' empty_subs)

build_subs :: [Atom] -> [Subs] -> [Atom] -> [Subs]
build_subs _ thetas [] = thetas
build_subs xs thetas (ra : ras) = build_subs xs thetas' ras where
    thetas' = build_subs_for_atom xs ra thetas

get_subs :: [Term] -> [Term] -> Subs -> Maybe Subs
get_subs (K k : es) (K k' : es') subs = case k' == k of
    True -> get_subs es es' subs
    False -> Nothing
get_subs (V v : es) (K k' : es') subs@(Subs m) = case Map.lookup (V v) m of
    Nothing -> get_subs es es' (Subs (Map.insert (V v) (K k') m))
    Just (K k) -> case k == k' of
        True -> get_subs es es' subs
        False -> Nothing
get_subs [] [] subs = Just subs

subs_term :: Term -> Subs -> Term
subs_term e (Subs subs) = case Map.lookup e subs of
    Nothing -> e
    Just e' -> e'

apply_subs :: Atom -> Subs -> Atom
apply_subs (A p es) subs = A p (map (\e -> subs_term e subs) es)

build_subs_for_atom :: [Atom] -> Atom -> [Subs] -> [Subs]
build_subs_for_atom xs ra thetas = concat (map (subs_for_theta xs ra) thetas)

subs_for_theta :: [Atom] -> Atom -> Subs -> [Subs]
subs_for_theta xs ra theta = map (combine_subs theta) thetas where
    thetas = all_subs_for_atom xs ra'
    ra' = apply_subs ra theta

combine_subs :: Subs -> Subs -> Subs
combine_subs (Subs m1) (Subs m2) = Subs (Map.union m1 m2)

all_subs_for_atom :: [Atom] -> Atom -> [Subs]
all_subs_for_atom xs (A (P True p) [t1, t2]) | p == equals_string = 
    case (t1, t2) of
        (K k1, K k2) -> if k1 == k2 then [empty_subs] else []
        (K k, V v) -> [Subs $ Map.fromList [(V v, K k)]]
        (V v, K k) -> [Subs $ Map.fromList [(V v, K k)]]
        (V v1, V v2) -> [Subs $ Map.fromList [(V v1, t), (V v2, t)] | t <- get_constants (Set.fromList xs)]
all_subs_for_atom xs (A (P False p) [t1, t2]) | p == equals_string = 
    case (t1, t2) of
        (K k1, K k2) -> if k1 /= k2 then [empty_subs] else []
        (K k, V v) -> [Subs $ Map.fromList [(V v, t)] | t <- get_constants (Set.fromList xs) List.\\ [K k]]
        (V v, K k) -> [Subs $ Map.fromList [(V v, t)] | t <- get_constants (Set.fromList xs) List.\\ [K k]]
        (V v1, V v2) -> [Subs $ Map.fromList [(V v1, t1), (V v2, t2)] | t1 <- get_constants (Set.fromList xs), t2 <- get_constants (Set.fromList xs), t1 /= t2] 
all_subs_for_atom xs x = Maybe.mapMaybe (subs_for_atom x) xs

subs_for_atom :: Atom -> Atom -> Maybe Subs
subs_for_atom (A p vs) (A p' ks) | p == p' = make_subs vs ks
subs_for_atom _ _ | otherwise = Nothing

make_subs :: [Term] -> [Term] -> Maybe Subs
make_subs es ks = get_subs es ks empty_subs

-- all_atoms includes the implicit not-equals between constants.
-- These atoms are not stored explicitly in the model, but are
-- computed as needed.
all_atoms :: Set.Set Atom -> Set.Set Atom
all_atoms ps = Set.union ps distincts where
    distincts = Set.fromList [A (P False equals_string) [K v1, K v2] | v1 <- all_constants ps, v2 <- all_constants ps, v1 /= v2]

all_constants :: Set.Set Atom -> [String]    
all_constants ps = List.nub (concat (map f (Set.toList ps))) where
    f (A _ ts) = map g ts
    g (K k) = k
    g (V _) = error $ "Expected constants only in atoms: " ++ show ps

do_n :: Int -> (a -> a) -> a -> a
do_n 0 _ a = a
do_n n f a = do_n (n-1) f (f a)

fixed_point :: Eq a => (a->a) -> a -> a
fixed_point f a = 
    if f a == a then a
    else fixed_point f (f a)

out_step :: Bool -> [Rule] -> Set.Set (Set.Set Atom) -> Set.Set (Set.Set Atom)
out_step do_update g as = Set.union as' (out_step1 do_update g as') where
    as' = Set.map (update_model do_update g) as

out_step1 :: Bool -> [Rule] -> Set.Set (Set.Set Atom) -> Set.Set (Set.Set Atom)
out_step1 do_update rs ms = Set.map (update_model do_update rs) $ Set.unions (map (out_step1m rs) (Set.toList ms))

out_step1m :: [Rule] -> Set.Set Atom -> Set.Set (Set.Set Atom)
out_step1m rs m = Set.unions (map (out_step1mr m) rs)

out_step1mr :: Set.Set Atom -> Rule -> Set.Set (Set.Set Atom)
out_step1mr m (Must as ds) = Set.unions (map (out_step_single m as) (Set.toList ds))
out_step1mr m (May as ds) = Set.unions (map (out_step_single m as) (Set.toList ds))

out_step_single :: Set.Set Atom -> Set.Set Atom -> Atom -> Set.Set (Set.Set Atom)
out_step_single m bs c = Set.unions (map (out_step_sub m c) (all_subs_for_lhs m bs))

out_step_sub :: Set.Set Atom -> Atom -> Subs -> Set.Set (Set.Set Atom)
out_step_sub m c subs = Set.fromList ass' where
    ass' = map remove_identities ass
    ass = map f (all_existential_subs m c subs)
    f subs' = Set.insert (apply_subs c subs') m

remove_identities_from_model :: Model -> Model
remove_identities_from_model Nothing = Nothing
remove_identities_from_model (Just ps) = Just (remove_identities ps)

remove_identities :: Set.Set Atom -> Set.Set Atom
remove_identities = Set.filter (not . f ) where
    f (A (P _ p) ts) = p == equals_string || any g ts 
    g (K k) = k == k_extra
    g (V _) = error "woah unexpected variable"

all_existential_subs :: Set.Set Atom -> Atom -> Subs -> [Subs]
all_existential_subs m c subs = map (combine_subs subs) (existential_subs ks vs) where    
    ks = all_constants m
    vs = free_vars (apply_subs c subs) 

free_vars :: Atom -> [String]    
free_vars a = List.nub $ f a where
    f (A _ ts) = Maybe.mapMaybe g ts
    g (V v) = Just v
    g (K _) = Nothing

rule_vars :: Rule -> [String]
rule_vars (Must as ds) = (List.sort . List.nub) (concat (map atom_vars (Set.toList as)) ++ concat (map atom_vars (Set.toList ds)))
rule_vars (May as ds) = (List.sort . List.nub) (concat (map atom_vars (Set.toList as)) ++ concat (map atom_vars (Set.toList ds)))

atom_vars :: Atom -> [String]
atom_vars (A _ ts) = Maybe.mapMaybe f ts where
    f (K _) = Nothing
    f (V v) = Just v

existential_subs :: [String] -> [String] -> [Subs]
existential_subs ks vs = List.foldl' f [empty_subs] vs where
    f ss v = concat (map (g v) ss)
    g v subs = map (extend_subs subs v) (all_constants subs)
    extend_subs (Subs m) v k = Subs (Map.insert (V v) (K k) m)
    all_constants (Subs m) = next_null (old_constants m) : old_constants m
    old_constants m = List.nub (ks ++ h m)
    h = map ( \(K k) -> k) . (Map.elems)

-- The index of the next null, 1 higher than any nulls in ks.
next_null :: [String] -> String
next_null ks = null_string ++ (show (max_null ks + 1))

-- The max null index in the list of constants.
max_null :: [String] -> Int
max_null ks = maximum (0 : map f ns) where
    ns = Maybe.mapMaybe g ks
    g k | List.isInfixOf null_string k = Just k
    g _ | otherwise = Nothing
    f k = read (drop (length null_string) k)

next_models :: Problem -> Model -> Set.Set Model
next_models p@(Problem rs _ do_update) m = Set.fromList x where
    n = Node m []
    x = map f (all_applications p n)
    f ap = do_application do_update rs m ap

all_applications :: Problem -> Node -> [Application]
all_applications (Problem rs _ _) n = concat (map (all_apps_for_rule n) xs) where
    xs = zip [0..] rs

all_apps_for_rule :: Node -> (Int, Rule) -> [Application]
all_apps_for_rule (Node Nothing _) _ = []
all_apps_for_rule (Node (Just m) _) (ri, r@(Must bs ds)) = concat (map f ss) where
    ss = all_subs_for_lhs m bs    
    f sub = concat (map (g sub) [0 .. length ds - 1])
    g sub di = map (h di) (all_existential_subs m (Set.toList ds !! di) sub)
    h di sub = Ap ri r sub di  
all_apps_for_rule (Node (Just m) _) (ri, r@(May bs ds)) = concat (map f ss) where
    ss = all_subs_for_lhs m bs    
    f sub = concat (map (g sub) [0 .. length ds - 1])
    g sub di = map (h di) (all_existential_subs m (Set.toList ds !! di) sub)
    h di sub = Ap ri r sub di  

find_valid_models :: Problem -> Int -> Set.Set (Set.Set Atom)
find_valid_models p n = find_valid_models2 (add_constraints p) n

find_valid_models2 :: Problem -> Int -> Set.Set (Set.Set Atom)
find_valid_models2 p@(Problem rs _ _) n = Set.fromList msl' where
    msl = Maybe.mapMaybe (valid_node rs) (Set.toList ms)
    ms = expand_tree p n
    msl' = map remove_identities msl

valid_node :: [Rule] -> Model -> Maybe (Set.Set Atom)
valid_node rs (Just m) = case valid_model rs m of
    True -> Just m
    False -> Nothing
valid_node _ _ = Nothing

expand_tree :: Problem -> Int -> Set.Set Model
expand_tree p@(Problem rs ps do_update) n = run_tree p (Set.singleton m) Set.empty 0 n where
    m = (Just ps')
    ps' = update_model do_update rs ps

run_tree :: Problem -> Set.Set Model -> Set.Set Model -> Int -> Int -> Set.Set Model    
run_tree _ currents prevs n n' | n >= n' = Set.union prevs currents
run_tree p currents prevs i n | otherwise = step where
    step = run_tree p nexts (Set.union prevs currents) (i+1) n    
    nexts = Set.unions (map (next_models p) (Set.toList currents))

make_constraint :: Rule -> Maybe Rule    
make_constraint (May _ _) = Nothing
make_constraint (Must bs hs) = case get_ex_vs bs hs of
    [] -> Just (Must (Set.union bs (Set.map complement hs)) Set.empty)
    _ -> Nothing

complement :: Atom -> Atom
complement (A (P b s) ts) = A (P (not b) s) ts

make_negation_from_constraint :: Rule -> [Rule]
make_negation_from_constraint (Must bs hs) | Set.null hs = [Must bs' hs' | 
    b <- Set.toList bs,
    bs' <- [Set.delete b bs],
    hs' <- [Set.singleton (complement b)],
    null (get_ex_vs bs' hs')
    ]
make_negation_from_constraint _ = []

add_constraints :: Problem -> Problem
add_constraints (Problem rs a f) = Problem rs2 a f where
    rs' = List.nub (rs ++ Maybe.mapMaybe make_constraint rs)
    rs2 = List.nub (rs' ++ concat (map make_negation_from_constraint rs'))

update_model :: Bool -> [Rule] -> Set.Set Atom -> Set.Set Atom
update_model False _ as = as
update_model True rs a = Set.union a a' where
    a' = intersections (filter f tvs)
    f tv = satisfies_all rs tv && Set.isSubsetOf a tv
    tvs = all_tvs all_as
    all_as = all_possible_atoms rs a

all_possible_atoms :: [Rule] -> Set.Set Atom -> [Atom]
all_possible_atoms rs as = concat (map (all_atoms_for_pred ks) ps) where
    ps = get_all_predicates rs as
    ks = (K k_extra) : get_all_constants rs as

k_extra :: String
k_extra = "extra"    

all_atoms_for_pred :: [Term] -> (Pred, Int) -> [Atom]    
all_atoms_for_pred ts (p, arity) = all_atoms_for_pred2 ts arity [A p []] 

all_atoms_for_pred2 :: [Term] -> Int -> [Atom] -> [Atom]
all_atoms_for_pred2 _ 0 acc = acc
all_atoms_for_pred2 ts arity acc = all_atoms_for_pred2 ts (arity-1) acc' where
    acc' = concat (map f acc)
    f a = map (g a) ts
    g (A p ts) t = A p (ts ++ [t])

get_all_predicates :: [Rule] -> Set.Set Atom -> [(Pred, Int)]
get_all_predicates rs a = List.nub (concat (map f rs) ++ map h (Set.toList a)) where
    f (Must bs hs) = map h (Set.toList bs ++ Set.toList hs)
    f (May bs hs) = map h (Set.toList bs ++ Set.toList hs)
    h (A (P _ p) ts) = (P True p, length ts)

get_all_constants :: [Rule] -> Set.Set Atom -> [Term]
get_all_constants rs as = List.nub ks where
    ks = g as ++ concat (map f rs)
    f (Must bs hs) = get_constants bs ++ get_constants hs
    f (May bs hs) = get_constants bs ++ get_constants hs
    g xs = map K (all_constants xs)

get_constants :: Set.Set Atom -> [Term]    
get_constants ps = List.nub (concat (map f (Set.toList ps))) where
    f (A _ ts) = Maybe.mapMaybe g ts
    g (K k) = Just (K k)
    g (V _) = Nothing

all_tvs :: [Atom] -> [Set.Set Atom]    
all_tvs [] = [Set.empty]
all_tvs (a:as) = x1 ++ x2 where
    x1 = map (Set.insert a) tvs
    x2 = map (Set.insert (set_polarity False a)) tvs
    tvs = all_tvs as

set_polarity :: Bool -> Atom -> Atom
set_polarity p (A (P _ s) ts) = A (P p s) ts

intersections :: Ord a => [Set.Set a] -> Set.Set a
intersections [] = Set.empty
intersections [x] = x
intersections (x:x':xs) = intersections (Set.intersection x x': xs)

---------------------------------- interaction --------------------------------

run :: Problem -> IO Node
run p@(Problem _ m _) = loop p' (Node (Just m) []) where
    p' = add_constraints p

loop :: Problem -> Node -> IO Node
loop p@(Problem rs _ _) n = do
    print_node n
    let (Node m aps) = n
    case is_valid m rs of
        True -> putStrLn "This is a valid model."
        False -> do
            putStrLn "This is an invalid model. Unsatisfied rules:"
            forM_ (invalid_rules m rs) $ \r -> do
                putStrLn $ "\t" ++ show r
    cr <- choose_rule rs
    case cr of
        CFinish -> return n
        CBack -> go_back p n
        CInvalid -> do
            putStrLn "Invalid choice"
            loop p n
        CRule k -> on_rule_chosen p n (k-1)

choose_rule :: [Rule] -> IO ChooseRule        
choose_rule rs = do
    putStrLn "Rules:"
    forM_ (zip [1..] rs) $ \(i,r) -> putStrLn $ "\t" ++ show i ++ ": " ++ show r
    putStrLn $ "Choose a rule [1.." ++ show (length rs) ++ "], or 'f' for Finish or 'b' for Back"
    k <- getLine
    case k !! 0 of 
        'f' -> return CFinish
        'F' -> return CFinish
        'b' -> return CBack
        'B' -> return CBack
        _ -> return $ try_read_int (length rs) k

try_read_int :: Int -> String -> ChooseRule
try_read_int n s = case readMaybeInt s of
    Nothing -> CInvalid
    Just k -> case k >= 1 && k <= n of
        True -> CRule k
        False -> CInvalid

readMaybeInt :: String -> Maybe Int
readMaybeInt = readMaybe

go_back :: Problem -> Node -> IO Node
go_back p@(Problem rs m do_update) (Node _ aps) = loop p n' where
    n' = Node m' aps'
    aps' = take (length aps - 1) aps
    m' = do_applications True rs (Just m) aps'

on_rule_chosen :: Problem -> Node -> Int -> IO Node
on_rule_chosen p@(Problem rs _ do_update) n i = do
    let r = rs !! i
    putStrLn $ "Choosing rule: " ++ show r
    let vs = rule_vars r
    ks <- interact_subs vs
    let theta = Subs (Map.fromList (zip (map V vs) (map K ks)))
    x <- interact_disjunct r
    let ap = Ap i r theta x
    let (Node m aps) = n
    case check_application m ap of
        False -> do
            putStrLn "!!!ERROR: Invalid substitution!!!"
            print ap
            on_rule_chosen p n i
        True -> do
            return n
            let m2 = do_application True rs m ap
            let n' = Node m2 (aps ++ [ap])
            loop p n'

do_application :: Bool -> [Rule] -> Model -> Application -> Model
do_application do_update rs m ap = update_maybe_model do_update rs m' where
    m' = remove_identities_from_model (do_app m ap)

update_maybe_model :: Bool -> [Rule] -> Model -> Model    
update_maybe_model _ _ Nothing = Nothing
update_maybe_model do_update rs (Just m) = Just (update_model do_update rs m)

do_app :: Model -> Application -> Model
do_app Nothing _ = Nothing
do_app _ (Ap _ (May _ ds) _ _) | Set.null ds = Nothing
do_app (Just m) (Ap _ (May _ disjs) theta i) = Just m' where
    m' = f m c
    c = Set.toList disjs !! i
    f x a = Set.insert (apply_subs a theta) x
do_app _ (Ap _ (Must _ ds) _ _) | Set.null ds = Nothing
do_app (Just m) (Ap _ (Must _ disjs) theta i) = Just m' where
    m' = f m c
    c = Set.toList disjs !! i
    f x a = Set.insert (apply_subs a theta) x

do_applications :: Bool -> [Rule] -> Model -> [Application] -> Model    
do_applications do_update rs m as = List.foldl' (do_application do_update rs) m as

check_application :: Model -> Application -> Bool
check_application Nothing _ = False
check_application (Just m) (Ap _ (Must as _) theta _) = all f as where
    f a = sat_ground_atom m (apply_subs a theta)
check_application (Just m) (Ap _ (May as _) theta _) = all f as where
    f a = sat_ground_atom m (apply_subs a theta)

sat_ground_atom :: Set.Set Atom -> Atom -> Bool    
sat_ground_atom _ (A (P True p) [t1, t2]) | p == equals_string = t1 == t2
sat_ground_atom _ (A (P False p) [t1, t2]) | p == equals_string = t1 /= t2
sat_ground_atom as a = Set.member a as

interact_subs :: [String] -> IO [String]    
interact_subs [] = return []
interact_subs (v: vs) = do
    k <- interact_const v
    ks <- interact_subs vs
    return (k: ks)

interact_const :: String -> IO String
interact_const var = do
    putStrLn $ "Enter substitution for " ++ var ++ " : "
    k <- getLine
    let oops = "oops"
    if length k > length oops then
        case drop (length k - length oops) k == oops of
            True -> interact_const var
            False -> return k

    else
        return k

interact_disjunct :: Rule -> IO Int
interact_disjunct (May _ ds) | Set.size ds <= 1 = return 0
interact_disjunct (May _ _) = return 0
interact_disjunct (Must _ ds) | Set.size ds <= 1 = return 0
interact_disjunct (Must _ ds) | otherwise = do
    putStrLn "Enter disjunct index: "
    x <- getLine
    case readMaybeInt x of
        Nothing -> return 0
        Just n -> case n >= 0 && n < length ds of
            True -> return n
            False -> return 0

print_node :: Node -> IO ()
print_node (Node m aps) = do
    putStrLn "Model:"
    case m of
        Nothing -> putStrLn "Invalid"
        Just xs -> forM_ (Set.toList xs) $ \p -> putStrLn $ "\t" ++ show p
    case null aps of
        True -> return ()
        False ->  do
            putStrLn "Applications:"
            forM_ aps $ \p -> putStrLn $ "\t" ++ show p

is_valid :: Model -> [Rule] -> Bool
is_valid Nothing _ = False
is_valid (Just m) rs = satisfies_all rs m

invalid_rules :: Model -> [Rule] -> [Rule]
invalid_rules Nothing _ = []
invalid_rules (Just m) rs = filter (not . satisfies_rule m) rs

instance Show Application where
    show (Ap n _ subs k) = show n ++ " " ++ show subs ++ " " ++ show k

---------------------------------- main ---------------------------------------

main = do
    test1
    test2
    test3
    test4
    test5
    test6
    test7
    test8
    test9
    test10
    test11
    test12
    test13

atomK1 :: String -> String -> Atom
atomK1 p x = A (P True p) [K x]

atomK2 :: String -> String -> String -> Atom
atomK2 p x y = A (P True p) [K x, K y]

neg_atomK1 :: String -> String -> Atom
neg_atomK1 p x = A (P False p) [K x]

neg_atomK2 :: String -> String -> String -> Atom
neg_atomK2 p x y = A (P False p) [K x, K y]

atomV1 :: String -> String -> Atom
atomV1 p x = A (P True p) [V x]

atomV2 :: String -> String -> String -> Atom
atomV2 p x y = A (P True p) [V x, V y]

atomV3 :: String -> String -> String -> String -> Atom
atomV3 p x y z = A (P True p) [V x, V y, V z]

neg_atomV1 :: String -> String -> Atom
neg_atomV1 p x = A (P False p) [V x]

neg_atomV2 :: String -> String -> String -> Atom
neg_atomV2 p x y = A (P False p) [V x, V y]

p1 = Problem [
    Must (Set.fromList [atomV1 "p" "X"]) (Set.fromList [atomV2 "q" "X" "Y"])
    ] (Set.fromList [atomK1 "p" "a"]) False

test1 :: IO ()
test1 = do
    let xs = find_valid_models p1 3
    let s1 = Set.fromList [atomK1 "p" "a", atomK2 "q" "a" "a"]
    let s2 = Set.fromList [atomK1 "p" "a", atomK2 "q" "a" "null1"]
    let s3 = Set.fromList [atomK1 "p" "a", atomK2 "q" "a" "a", atomK2 "q" "a" "null1"]
    forM_ (Set.toList xs) print
    HUnit.assertBool "Test1 " $ s1 `Set.member` xs
    HUnit.assertBool "Test1 " $ s2 `Set.member` xs
    HUnit.assertBool "Test1 " $ s3 `Set.member` xs
    putStrLn "OK"

p2 = Problem [
    Must (Set.empty) (Set.fromList [atomV1 "p" "X"]),
    Must (Set.fromList [atomV1 "p" "X", atomV1 "p" "Y"]) (Set.fromList [atomV2 equals_string "X" "Y"])
    ] Set.empty False

test2 :: IO ()
test2 = do
    let xs = find_valid_models p2 3
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [atomK1 "p" "null1"]
    HUnit.assertBool "Test2 " $ s1 `Set.member` xs
    putStrLn "OK"

p3 = Problem [
    Must (Set.empty) (Set.fromList [atomV1 "zero" "X"]),
    Must (Set.singleton (atomV1 "zero" "X")) (Set.singleton (atomV1 "nat" "X")),
    Must (Set.fromList [atomV1 "zero" "X", atomV1 "zero" "Y"]) (Set.fromList [atomV2 equals_string "X" "Y"]),
    May (Set.fromList [atomV1 "nat" "X"]) (Set.fromList [atomV2 "succ" "X"  "Y"]),
    Must (Set.fromList [atomV2 "succ" "X" "Y", atomV2 "succ" "X" "Z"]) (Set.fromList [atomV2 equals_string "Y" "Z"]),
    Must (Set.fromList [atomV2 "succ" "X" "Y"]) (Set.fromList [atomV1 "nat" "Y"]),
    Must (Set.fromList [atomV2 "succ" "X" "Y"]) (Set.fromList [neg_atomV2 equals_string "X" "Y"]),
    Must (Set.fromList [atomV2 "succ" "X" "Y"]) (Set.fromList [atomV2 "less" "X" "Y"]),
    Must (Set.fromList [atomV2 "succ" "X" "Y", atomV2 "less" "Y" "Z"]) (Set.fromList [atomV2 "less" "X" "Z"]),
    Must (Set.fromList [atomV2 "less" "X" "X"]) Set.empty
    ] Set.empty False

test3 :: IO ()
test3 = do
    let xs = find_valid_models p3 8
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [atomK1 "nat" "null1", atomK1 "zero" "null1", neg_atomK2 "succ" "null1" "null1"]
    let s2 = Set.fromList [atomK1 "nat" "null1", atomK1 "nat" "null2", atomK1 "zero" "null1", atomK2 "succ" "null1" "null2", atomK2 "less" "null1" "null2", neg_atomK2 "succ" "null1" "null1", neg_atomK2 "succ" "null2" "null2", neg_atomK1 "zero" "null2"]
    HUnit.assertBool "Test3 " $ Set.size xs == 2
    HUnit.assertBool "Test3 " $ s1 `Set.member` xs
    HUnit.assertBool "Test3 " $ s2 `Set.member` xs
    putStrLn "OK"

p4 = Problem [
    Must (Set.fromList [atomV1 "p" "X"]) (Set.fromList [atomV2 "q" "X" "Y"])
    ] (Set.fromList [atomK1 "p" "a", atomK1 "r" "b"]) False

test4 :: IO ()
test4 = do
    let xs = find_valid_models p4 1
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [atomK1 "p" "a", atomK2 "q" "a" "a", atomK1 "r" "b"]
    let s2 = Set.fromList [atomK1 "p" "a", atomK2 "q" "a" "b", atomK1 "r" "b"]
    let s3 = Set.fromList [atomK1 "p" "a", atomK2 "q" "a" "null1", atomK1 "r" "b"]
    HUnit.assertBool "Test4 " $ s1 `Set.member` xs
    HUnit.assertBool "Test4 " $ s2 `Set.member` xs
    HUnit.assertBool "Test4 " $ s3 `Set.member` xs
    putStrLn "OK"

p5 = Problem [
    Must (Set.empty) (Set.fromList [atomV1 "p" "X"]),
    Must (Set.empty) (Set.fromList [atomV1 "q" "X"]),
    Must (Set.empty) (Set.fromList [atomV1 "r" "X"]),
    Must (Set.fromList [atomV1 "r" "X"]) (Set.fromList [atomV1 "p" "X"]),    
    Must (Set.fromList [atomV1 "r" "X"]) (Set.fromList [atomV1 "q" "X"])
    ] (Set.fromList [atomK1 "p" "a", atomK1 "q" "b"]) False

test5 :: IO ()
test5 = do
    let xs = find_valid_models p5 2
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [atomK1 "p" "a", atomK1 "p" "b", atomK1 "q" "b", atomK1 "r" "b"]
    let s2 = Set.fromList [atomK1 "p" "a", atomK1 "q" "a", atomK1 "q" "b", atomK1 "r" "a"]
    HUnit.assertBool "Test5 " $ s1 `Set.member` xs
    HUnit.assertBool "Test5 " $ s2 `Set.member` xs
    putStrLn "OK"

p6 = Problem [
    May Set.empty (Set.singleton (atomV2 "r" "X" "Y")),
    Must (Set.singleton (atomV2 "r" "X" "Y")) (Set.singleton (atomV2 equals_string "X" "Y")),
    Must (Set.singleton (atomV2 "r" "X" "Y")) (Set.singleton (atomV1 "p" "X")),
    Must (Set.singleton (atomV2 "r" "X" "Y")) (Set.singleton (atomV1 "q" "Y"))
    ] Set.empty False

test6 :: IO ()
test6 = do
    let xs = find_valid_models p6 3
    forM_ (Set.toList xs) print
    let s1 = Set.empty
    let s2 = Set.fromList [atomK1 "p" "null1", atomK1 "q" "null1", atomK2 "r" "null1" "null1"]
    HUnit.assertBool "Test6 " $ s1 `Set.member` xs
    HUnit.assertBool "Test6 " $ s2 `Set.member` xs
    putStrLn "OK"

p7 = Problem [
    May Set.empty (Set.singleton (atomV2 "r" "X" "Y")),
    Must (Set.singleton (atomV2 "r" "X" "Y")) (Set.singleton (neg_atomV2 equals_string "X" "Y")),
    Must (Set.singleton (atomV2 "r" "X" "Y")) (Set.singleton (atomV1 "p" "X")),
    Must (Set.singleton (atomV2 "r" "X" "Y")) (Set.singleton (atomV1 "q" "Y"))
    ] Set.empty False

test7 :: IO ()
test7 = do
    let xs = find_valid_models p7 5
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [atomK1 "p" "null1", atomK1 "q" "null2", atomK2 "r" "null1" "null2", neg_atomK2 "r" "null1" "null1", neg_atomK2 "r" "null2" "null2"]
    let s2 = Set.fromList []
    HUnit.assertBool "Test7 " $ Set.size xs == 2
    HUnit.assertBool "Test7 " $ s1 `Set.member` xs
    HUnit.assertBool "Test7 " $ s2 `Set.member` xs
    putStrLn "OK"

p8 = Problem [
    Must Set.empty (Set.fromList [atomV1 "jack" "X"]),
    Must (Set.fromList [atomV1 "jack" "X"]) (Set.fromList [atomV1 "man" "X"]),
    Must (Set.fromList [atomV1 "man" "X"]) (Set.fromList [atomV1 "mortal" "X"]),
    Must (Set.fromList [atomV1 "jack" "X", atomV1 "jack" "Y"]) (Set.fromList [atomV2 equals_string "X" "Y"])
    ] Set.empty False

test8 :: IO ()
test8 = do
    let xs = find_valid_models p8 3
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [atomK1 "jack" "null1", atomK1 "man" "null1", atomK1 "mortal" "null1"]
    HUnit.assertBool "Test8 " $ Set.size xs == 1
    HUnit.assertBool "Test8 " $ s1 `Set.member` xs
    putStrLn "OK"

p9 = Problem [
    Must (Set.fromList [atomV1 "p" "X"]) (Set.fromList [atomV1 "q" "X"]),
    Must (Set.fromList [atomV1 "p" "X"]) (Set.fromList [atomV1 "r" "X"])
    ] 
    (Set.singleton (atomK1 "p" "a")) False

test9 :: IO ()
test9 = do
    let xs = find_valid_models p9 3
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [atomK1 "p" "a", atomK1 "q" "a", atomK1 "r" "a"]
    HUnit.assertBool "Test13 " $ Set.size xs == 1
    HUnit.assertBool "Test13 " $ s1 `Set.member` xs

p10 = Problem [
    Must (Set.fromList [atomV1 "conference_paper" "X"]) (Set.fromList [atomV1 "article" "X"]),
    Must (Set.fromList [atomV1 "journal_paper" "X"]) (Set.fromList [atomV1 "article" "X"]),
    Must (Set.fromList [atomV1 "conference_paper" "X"]) (Set.fromList [neg_atomV1 "journal_paper" "X"]),
    Must (Set.fromList [atomV1 "scientist" "X"]) (Set.fromList [atomV2 "is_author_of" "X" "Y"]),
    Must (Set.fromList [atomV2 "is_author_of" "X" "Y"]) (Set.fromList [atomV1 "scientist" "X"]),
    Must (Set.fromList [atomV2 "is_author_of" "X" "Y"]) (Set.fromList [atomV1 "article" "Y"]),
    Must (Set.fromList [atomV2 "is_author_of" "X" "Y"]) (Set.fromList [atomV2 "has_author" "Y" "X"]),
    Must (Set.fromList [atomV2 "has_author" "X" "Y"]) (Set.fromList [atomV2 "is_author_of" "Y" "X"]),
    Must (Set.fromList [atomV2 "has_first_author" "X" "Y", atomV2 "has_first_author" "X" "Y2"]) (Set.fromList [atomV2 equals_string "Y" "Y2"]) ] (Set.fromList [
        atomK1 "scientist" "s1",
        atomK2 "is_author_of" "s1" "j1",
        atomK1 "article" "j1"
        ]) False

test10 :: IO ()
test10 = do
    let xs = find_valid_models p10 3
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [atomK1 "article" "j1", atomK2 "has_author" "j1" "s1", atomK2 "is_author_of" "s1" "j1", atomK1 "scientist" "s1"]
    HUnit.assertBool "Test10 " $ Set.size xs == 1
    HUnit.assertBool "Test10 " $ s1 `Set.member` xs
    putStrLn "OK"

p11 = Problem [
    Must (Set.fromList [atomV1 "p" "X"]) (Set.fromList [atomV1 "q" "X"]),
    Must Set.empty (Set.fromList [neg_atomV1 "q" "X"])
    ] Set.empty False

test11 :: IO ()
test11 = do
    print p11
    let xs = find_valid_models p11 4
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [neg_atomK1 "p" "null1", neg_atomK1 "q" "null1"]
    let s2 = Set.fromList [neg_atomK1 "p" "null1", neg_atomK1 "q" "null1", neg_atomK1 "p" "null2", neg_atomK1 "q" "null2"]
    HUnit.assertBool "Test11 " $ Set.size xs == 2
    HUnit.assertBool "Test11 " $ s1 `Set.member` xs
    HUnit.assertBool "Test11 " $ s2 `Set.member` xs
    putStrLn "OK"

p12 = Problem [
    Must (Set.fromList [atomV1 "p" "X", neg_atomV1 "q" "X"]) Set.empty,
    Must Set.empty (Set.fromList [atomV1 "p" "X"])
    ] Set.empty False

test12 :: IO ()
test12 = do
    print p12
    let xs = find_valid_models p12 4
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [atomK1 "p" "null1", atomK1 "q" "null1"]
    let s2 = Set.fromList [atomK1 "p" "null1", atomK1 "q" "null1", atomK1 "p" "null2", atomK1 "q" "null2"]
    HUnit.assertBool "Test12 " $ Set.size xs == 2
    HUnit.assertBool "Test12 " $ s1 `Set.member` xs
    HUnit.assertBool "Test12 " $ s2 `Set.member` xs
    putStrLn "OK"

p13 = Problem [
    Must (Set.fromList [atomV1 "p" "X", atomV1 "q" "X"]) Set.empty,
    Must (Set.fromList [neg_atomV1 "p" "X", atomV1 "q" "X"]) Set.empty,
    Must Set.empty (Set.fromList [atomV1 "r" "X"])
    ] Set.empty True

test13 :: IO ()
test13 = do
    print p13
    let xs = find_valid_models p13 2
    forM_ (Set.toList xs) print
    let s1 = Set.empty
    let s2 = Set.fromList [atomK1 "r" "null1", neg_atomK1 "q" "null1"]
    let s3 = Set.fromList [atomK1 "r" "null1", neg_atomK1 "q" "null1", atomK1 "r" "null2", neg_atomK1 "q" "null2"]
    HUnit.assertBool "Test13 " $ Set.size xs == 3
    HUnit.assertBool "Test13 " $ s1 `Set.member` xs
    HUnit.assertBool "Test13 " $ s2 `Set.member` xs
    HUnit.assertBool "Test13 " $ s3 `Set.member` xs
    putStrLn "OK"

p14 = Problem [
    Must (Set.fromList [atomV1 "p" "X"]) (Set.fromList [atomV2 "q" "X" "Y"])
    ] (Set.fromList [neg_atomK2 "q" "a" "a"]) True

test14 :: IO ()
test14 = do
    let xs = find_valid_models p14 4
    forM_ (Set.toList xs) print
    let s1 = Set.fromList [neg_atomK2 "q" "a" "a"]
    HUnit.assertBool "Test14 " $ Set.size xs == 1
    HUnit.assertBool "Test1 " $ s1 `Set.member` xs
    putStrLn "OK"

p15 = Problem [
    Must (Set.fromList [atomV2 "p" "X" "Y"]) (Set.fromList [atomV1 "q" "X"])
    ] (Set.fromList [neg_atomK1 "q" "a"]) True

test15 :: IO ()
test15 = do
    let xs = find_valid_models p15 4
    forM_ (Set.toList xs) print

