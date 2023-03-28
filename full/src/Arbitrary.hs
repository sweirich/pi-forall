-- | This module is for testing the parser/pretty printer. 
-- We would like to satisfy the following roundtrip property: 
--     * if we generate a random AST term and print it, then it should parse back to an alpha-equivalent term

module Arbitrary where

import qualified Data.Set as Set
import Test.QuickCheck
    ( elements, frequency, sized, Arbitrary(arbitrary), Gen ) 
import qualified Test.QuickCheck as QC
import qualified Unbound.Generics.LocallyNameless as Unbound
import Text.Parsec.Error ( ParseError )

import Syntax
import PrettyPrint ( render, Disp(disp) )
import Parser ( testParser, expr )


-- | Round trip property: a given term prints then parses to the same term.
prop_roundtrip :: Term -> QC.Property
prop_roundtrip tm = 
    let str = render (disp tm) in
    case test_parseExpr str  of
        Left _ -> QC.counterexample ("*** Could not parse:\n" ++ str) False
        Right tm' -> QC.counterexample ("*** Round trip failure! Parsing:\n" ++ str ++ "\n*** results in\n" ++ show tm') (Unbound.aeq tm tm')
           
test_parseExpr :: String -> Either Text.Parsec.Error.ParseError Term
test_parseExpr = testParser arbConstructorNames expr

-- View random terms
sampleTerms :: IO ()
sampleTerms = QC.sample' (arbitrary :: Gen Term) >>= 
    mapM_ (putStrLn . render . disp)

---------------------------------------------------------------------------------------------------
-- Generators for the pi-forall expression AST
-- These generation functions and Arbitrary instances are tailored for testing the pretty printer 
-- and parser. As a result, they do not generate "unprintable" parts of the AST, such as type annotations
-- and source code positions.


-- * Names

-- | variable names 
-- drawn from a small list
genName :: Gen (Unbound.Name a)
genName = Unbound.string2Name <$> elements ["x", "y", "z", "x0" , "y0"]

instance Arbitrary (Unbound.Name a) where
    arbitrary = genName

tcNames :: [TCName]
tcNames = ["T", "List", "Vec" ]
dcNames :: [DCName]
dcNames = ["K", "Nil", "Cons"]

arbConstructorNames :: ConstructorNames
arbConstructorNames = ConstructorNames (Set.fromList tcNames) (Set.fromList dcNames)

genTCName :: Gen TCName
genTCName = elements tcNames

genDCName :: Gen DCName
genDCName = elements dcNames


-- * Core language

-- Terms with no subterms
base :: Gen Term
base = elements [Type, TrustMe, PrintMe,
                tyUnit, litUnit, tyBool, 
                litTrue, litFalse, Refl  ]
    where tyUnit = TCon "Unit" [] 
          litUnit = DCon "()" [] 
          tyBool = TCon "Bool" [] 
          litTrue = DCon "True" [] 
          litFalse = DCon "False" [] 

-- Generate a random term
-- In the inner recursion, the bool prevents the generation of TCon/DCon applications 
-- inside Apps --- we want these terms to be fully saturated.
genTerm :: Int -> Gen Term
genTerm n
    | n <= 1 = base
    | otherwise = go True n where
        go b n0 = 
            let n' = n0 `div` 2 in
            frequency [
              (1, Var <$> genName),
              (1, genLam n'),
              (1, App <$> go False n' <*> genArg  n'),
              (1, genPi n'),
              (1, genLet n'),
                            (1, TyEq <$> go True n' <*> go True n'),
              (1, Subst <$> go True n' <*> go True n'),
              (1, Contra <$> go True n'),
              
                            (if b then 1 else 0, TCon <$> genTCName <*> genArgs n'),
              (if b then 1 else 0, DCon <$> genDCName <*> genArgs n'),
              (1, Case <$> go True n' <*> genBoundedList 2 (genMatch n')),
              
              (1, base)
            ]

genLam :: Int -> Gen Term
genLam n = do 
    p <- genName
    ep <- arbitrary 
    b <- genTerm n
    return $ Lam ep (Unbound.bind p b)


genPi :: Int -> Gen Term
genPi n = do 
    p <- genName
    ep <- arbitrary 
    tyA <- genTerm n
    tyB <- genTerm n
    return $ Pi ep tyA (Unbound.bind p tyB)

genSigma :: Int -> Gen Term
genSigma n = do
    p <- genName 
    tyA <- genTerm n
    tyB <- genTerm n
    l <- arbitrary
    return $ Sigma tyA l (Unbound.bind p tyB)

genLet :: Int -> Gen Term 
genLet n = do
    p <- genName 
    rhs <- genTerm n
    b <- genTerm n
    return $ Let rhs (Unbound.bind p b)

genLetPair :: Int -> Gen Term 
genLetPair n = do
    p <- (,) <$> genName <*> genName 
    a <- genTerm n
    b <- genTerm n
    return $ LetPair a (Unbound.bind p b)

instance Arbitrary Arg where
    arbitrary = sized genArg
    shrink (Arg ep tm) = 
        [ Arg ep tm' | tm' <- QC.shrink tm]

genArg :: Int -> Gen Arg
genArg n = Arg <$> arbitrary <*> genTerm (n `div` 2)

genArgs :: Int -> Gen [Arg]
genArgs n = genBoundedList 2 (genArg n)
        
instance Arbitrary Rho where
    arbitrary = elements [ Rel, Irr ]
instance Arbitrary Level where
    arbitrary = elements [ LConst 0, LConst 1, LConst 2, LConst 3]
instance Arbitrary Epsilon where
    arbitrary = Mode <$> arbitrary <*> arbitrary

genPattern :: Int -> Gen Pattern
genPattern n | n == 0 = PatVar <$> genName
  | otherwise = frequency 
    [(1, PatVar <$> genName),
     (1, PatCon <$> genDCName <*> genPatArgs)]
     where 
        n' = n `div` 2
        genPatArgs = genBoundedList 2 ( (,) <$> genPattern n' <*> arbitrary )

genMatch :: Int -> Gen Match
genMatch n = Match <$> (Unbound.bind <$> genPattern n <*> genTerm n)

instance Arbitrary Pattern where
    arbitrary = sized genPattern 
    shrink (PatCon n pats) = map fst pats ++ [PatCon n pats' | pats' <- QC.shrink pats]
    shrink _ = []

instance Arbitrary Match where
    arbitrary = sized genMatch
    shrink (Match bnd) = []


instance Arbitrary Term where
    arbitrary = sized genTerm

    -- when QC finds a counterexample, it tries to shrink it to find a smaller one
    shrink (App tm arg) = 
        [tm, unArg arg] ++ [App tm' arg | tm' <- QC.shrink tm] 
                        ++ [App tm arg' | arg' <- QC.shrink arg]

    shrink (Lam ep bnd) = []
    shrink (Pi ep tyA bnd) = [tyA]
    shrink (Let rhs bnd) = [rhs]
    shrink (Sigma tyA lvl bnd) = [tyA]
    shrink (TyEq a b) = [a,b] ++ [TyEq a' b | a' <- QC.shrink a] ++ [TyEq a b' | b' <- QC.shrink b]
    shrink (Subst a b) = [a,b] ++ [Subst a' b | a' <- QC.shrink a] ++ [Subst a b' | b' <- QC.shrink b]
    shrink (Contra a) = [a] ++ [Contra a' | a' <- QC.shrink a]
    
    shrink (TCon n as) = map unArg as ++ [TCon n as' | as' <- QC.shrink as]
    shrink (DCon n as) = map unArg as ++ [DCon n as' | as' <- QC.shrink as]
    shrink (Case a ms) = [a] ++ [Case a' ms | a' <- QC.shrink a] ++ [Case a ms' | ms' <- QC.shrink ms]
    
    shrink _ = []
       
-------------------------------------------------------
-- * General quickcheck utilities

-- | Only generate lists up to size n
genBoundedList :: Int -> Gen a -> Gen [a]
genBoundedList b g = do
  len <- QC.elements [0 .. b]
  take len <$> QC.infiniteListOf g

-- | Run quickcheck for more than 100 tests
quickCheckN :: QC.Testable prop => Int -> prop -> IO ()
quickCheckN n = QC.quickCheckWith $ QC.stdArgs { QC.maxSuccess = n , QC.maxSize = 100 }