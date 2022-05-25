module Arbitrary where

import Test.QuickCheck
    ( elements, frequency, sized, Arbitrary(arbitrary), Gen ) 
import qualified Test.QuickCheck as QC

import Syntax
import PrettyPrint
import Parser

import qualified Unbound.Generics.LocallyNameless as Unbound

bindSize :: Int
bindSize = 1

prop_roundtrip :: Term -> Bool
prop_roundtrip tm = 
    case parseExpr (render (disp tm))  of
        Left _ -> False
        Right tm' -> Unbound.aeq tm tm' 
           
quickCheckN :: QC.Testable prop => Int -> prop -> IO ()
quickCheckN n = QC.quickCheckWith $ QC.stdArgs { QC.maxSuccess = n , QC.maxSize = 100 }

sampleName :: IO ()
sampleName = QC.sample' (arbitrary :: Gen TName) >>= 
    mapM_ (print . render . disp)

sampleTerm :: IO ()
sampleTerm = QC.sample' (arbitrary :: Gen Term) >>= 
    mapM_ (print . render . disp)


-- variable names that are not reserved words
genName :: Gen (Unbound.Name a)
genName = Unbound.string2Name <$> elements ["x", "y", "z", "x0" , "y0"]

{- SOLN DATA -}
genTCName :: Gen TCName
genTCName = elements ["T", "List", "Vec", "Nat"]

genDCName :: Gen DCName
genDCName = elements ["Nil", "Cons", "Zero"]
{- STUBWITH -}

instance Arbitrary (Unbound.Name a) where
    arbitrary = genName
        
{- SOLN EP -}        
instance Arbitrary Epsilon where
    arbitrary = elements [ Rel, Irr ]
{- STUBWITH -}

instance Arbitrary Arg where
    arbitrary = sized genArg
    shrink (Arg {- SOLN EP -} ep {- STUBWITH -} tm) = [ Arg {- SOLN EP -} ep {- STUBWITH -} tm' | tm' <- QC.shrink tm]

genArg :: Int -> Gen Arg
genArg n = Arg <$> {- SOLN EP -} arbitrary <*> {- STUBWITH -} genTerm (n `div` 2)

genArgs :: Int -> Gen [Arg]
genArgs n = QC.listOf (genArg n)

base :: Gen Term
base = elements [Type, 
                TrustMe, PrintMe
                {- TyUnit, LitUnit, TyBool, 
                LitBool True, LitBool False -} {- SOLN EQUAL -} , Refl {- STUBWITH -} ]

genTerm :: Int -> Gen Term
genTerm n 
        | n <= 1 = base
        | otherwise = 
            frequency [

              (1, Var <$> genName),
              (1, genLam n'),
              (1, App <$> genTerm n' <*> genArg n'),
              (1, genPi n'),
              (1, Ann <$> genTerm n' <*> genTerm n'),
              (1, Pos internalPos <$> genTerm n'),
              (1, genLet n'),
              (1, If <$> genTerm n' <*> genTerm n' <*> genTerm n'),
              (1, genSigma n'),
              (1, Prod <$> genTerm n' <*> genTerm n'),
              (1, genLetPair n'),
              {- SOLN EQUAL -}
              (1, TyEq <$> genTerm n' <*> genTerm n'),
              (1, Subst <$> genTerm n' <*> genTerm n'),
              (1, Contra <$> genTerm n'),
              {- STUBWITH -}
              {- SOLN DATA -}
              (1, TCon <$> genTCName <*> genArgs n'),
              (1, DCon <$> genDCName <*> genArgs n'),
              (1, Case <$> genTerm n' <*> genMatches n'),
              {- STUBWITH -}
              (1, base)
            ]
    where n' = n `div` 2

genLam :: Int -> Gen Term
genLam n = do 
{- SOLN EP -}
    p <- (,) <$> genName <*> arbitrary  
    {- STUBWITH     p <- genName -}
    b <- genTerm n
    return $ Lam (Unbound.bind p b)

genPi :: Int -> Gen Term
genPi n = do 
{- SOLN EP -}
    p <- (,,) <$> genName <*> arbitrary <*> (Unbound.Embed <$> genTerm n)
    {- STUBWITH     p <- (,) <$> genName <*> (Unbound.Embed <$> genTerm n) -}
    tyB <- genTerm n
    return $ Pi (Unbound.bind p tyB)

genSigma :: Int -> Gen Term
genSigma n = do
    p <- (,) <$> genName <*> (Unbound.Embed <$> genTerm n)
    tyB <- genTerm n
    return $ Sigma (Unbound.bind p tyB)

genLet :: Int -> Gen Term 
genLet n = do
    p <- (,) <$> genName <*> (Unbound.Embed <$> genTerm n')
    b <- genTerm n'
    return $ Let (Unbound.bind p b)
  where n' = n `div` 2

genLetPair :: Int -> Gen Term 
genLetPair n = do
    p <- (,) <$> genName <*> genName 
    a <- genTerm n'
    b <- genTerm n'
    return $ LetPair a (Unbound.bind p b)
  where n' = n `div` 2

{- SOLN DATA -}
genPattern :: Int -> Gen Pattern
genPattern n | n == 0 = PatVar <$> genName
  | otherwise = frequency 
    [(1, PatVar <$> genName),
     (1, PatCon <$> genDCName <*> genPatArgs n')]
     where n' = n `div` 2

genPatArgs :: Int -> Gen [(Pattern, Epsilon)]
genPatArgs n = QC.listOf ( (,) <$> genPattern n <*> arbitrary )

genMatch :: Int -> Gen Match
genMatch n = Match <$> (Unbound.bind <$> genPattern n <*> genTerm n)
  
genMatches :: Int -> Gen [Match]
genMatches n = QC.listOf (genMatch n)

instance Arbitrary Pattern where
    arbitrary = sized genPattern 
    shrink (PatCon _ pats) = map fst pats
    shrink _ = []
{- STUBWITH -}

instance Arbitrary Term where
    arbitrary = sized genTerm
    shrink (App tm arg) = 
        [tm, unArg arg] ++ [App tm' arg | tm' <- QC.shrink tm] ++ [App tm arg' | arg' <- QC.shrink arg]
    shrink (Ann tm ty) = tm : [Ann tm' ty | tm' <- QC.shrink tm]
    shrink _ = []
       
