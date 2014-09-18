{-# LANGUAGE ScopedTypeVariables #-}

module Tester where

import Data.Maybe
import Data.List
import Test.QuickCheck
import Control.Monad
import System.Timeout
import System.IO.Unsafe

data Action c =
    In c
  | Out c
  | Tau
  deriving (Show, Eq, Ord)

instance Arbitrary c => Arbitrary (Action c) where
  arbitrary = oneof [liftM In arbitrary, liftM Out arbitrary, return Tau]
  shrink (In c) = Tau : Out c : map In (shrink c)
  shrink (Out c) = Tau : map Out (shrink c)
  shrink Tau = []

matches :: Eq c => Action c -> Action c -> Bool
matches (In c1) (Out c2) = c1==c2
matches (Out c1) (In c2) = c1==c2
matches _ _ = False

data CCS c = 
    Nil
  | Act (Action c) (CCS c)
  | Par (CCS c) (CCS c)
  | Alt (CCS c) (CCS c)
  -- | Repl (CCS c) 
  deriving Show

arbccs 0 = return Nil
arbccs n = oneof [arbccs 0, 
                  liftM2 Act arbitrary (arbccs (n-1)), 
                  liftM2 Par smaller smaller, 
                  liftM2 Alt smaller smaller]
  where smaller = arbccs (n `div` 2)

instance Arbitrary c => Arbitrary (CCS c) where
  arbitrary = sized arbccs
  shrink Nil = []
  shrink (Act a p) = p : map (uncurry Act) (shrink (a,p))
  shrink (Par p1 p2) = p1 : p2 : map (uncurry Par) (shrink (p1,p2))
  shrink (Alt p1 p2) = p1 : p2 : map (uncurry Alt) (shrink (p1,p2))

step :: Ord c => CCS c -> [(Action c, CCS c)]
step Nil = []
step (Act a c) = [(a,c)]
step (Par p1 p2) =    [(a,p1' `Par` p2) | (a,p1') <- p1e]
                     ++ [(a,p1 `Par` p2') | (a,p2') <- p2e]
                     ++ [(Tau,p1' `Par` p2') | (a1,p1') <- p1e, 
                                               (a2,p2') <- p2e, 
                                               a1 `matches` a2]
                     where p1e = step p1
                           p2e = step p2
step (Alt p1 p2) =  step p1 ++ step p2

(~~) :: Ord c => CCS c -> CCS c -> Bool
p1 ~~ p2 = p1a == p2a
           && all (\(a,p1') -> any (\(b,p2') -> a==b && p1' ~~ p2') p2e) p1e
           && all (\(a,p2') -> any (\(b,p1') -> a==b && p1' ~~ p2') p1e) p2e
  where p1e = step p1
        p2e = step p2
        p1a = sort (nub (map fst p1e))
        p2a = sort (nub (map fst p2e))

p1 ~^~ p2 = looksLike $ p1 ~~ p2

looksLike p =
  unsafePerformIO $
    do m <- timeout 100000 $ p `seq` return  p
       return $ maybe (False ==> True) property m

smallccs :: Arbitrary a =>   Gen (CCS a)
smallccs = sized (\n -> resize (min n 15) arbitrary)

newtype SmallCCS a = SmallCCS (CCS a)
  deriving Show

instance Arbitrary a => Arbitrary (SmallCCS a) where
  arbitrary = liftM SmallCCS smallccs
  shrink (SmallCCS p) = map SmallCCS (shrink p)

prop_refl (SmallCCS p :: SmallCCS Bool) = p ~^~ p

prop_alt_nil_zero (SmallCCS p :: SmallCCS Bool) = p ~^~ Alt Nil p

prop_alt_idempotent (SmallCCS p :: SmallCCS Bool) = Alt p p ~^~ p

prop_alt_symmetric (SmallCCS p) (SmallCCS q) = Alt p q ~^~ Alt q p

prop_par_nil_zero (SmallCCS p :: SmallCCS Bool) = p ~^~ Par Nil p

prop_par_idempotent (SmallCCS p :: SmallCCS Bool) = expectFailure $ Par p p ~^~ p

prop_par_symmetric (SmallCCS p :: SmallCCS Bool) (SmallCCS q :: SmallCCS Bool) =
  Par p q ~^~ Par q p

prop_alt_is_not_par (SmallCCS p :: SmallCCS Bool) (SmallCCS q :: SmallCCS Bool) =
  Par p q ~^~ Alt p q

prop_three_is_not_four (SmallCCS p :: SmallCCS Bool) =
  foldr1 Par [p,p,p,p] ~^~ foldr1 Par [p,p,p]

prop_bisimilarity a (SmallCCS p :: SmallCCS Bool) (SmallCCS q :: SmallCCS Bool) =
  Act a (Alt p q) ~^~ Alt (Act a p) (Act a q)

prop_act_par a (SmallCCS p :: SmallCCS Bool) (SmallCCS q :: SmallCCS Bool) =
  Par (Act a p) q ~^~ Act a (Par p q)

prop_Wrong3 m p q =
  expectFailure $
    Act m (Par p q) ~~ (Par (Act m p) (Act m q))

prop_ccs :: CCS Bool -> Property
prop_ccs p = collect (length (show p)) True

bad = Par (Act Tau (Par (Alt (Act Tau Nil) (Act Tau Nil)) (Act Tau Nil))) (Act Tau (Par Nil (Act Tau (Par (Act (Out False) Nil) (Act Tau Nil)))))

prop_trivial :: CCS Bool -> CCS Bool -> Bool
prop_trivial = (~~)

simCounterexampleGen :: Ord c => CCS c -> CCS c -> Gen (Maybe ([Action c], CCS c))
simCounterexampleGen p1 p2 = if p1a /= p2a then return (Just ([],p1))
                             else if p1a == [] then return Nothing 
                             else do (a,p1') <- elements p1e
                                     p2' <- elements [p2' | (a2,p2') <- p2e, a2==a]
                                     ce <- simCounterexampleGen p1' p2'
                                     case ce of 
                                       Nothing -> return Nothing
                                       Just (path,p1'') -> return (Just (a:path,p1''))
  where p1e = step p1
        p2e = step p2
        p1a = sort (nub (map fst p1e))
        p2a = sort (nub (map fst p2e))

prop_sim :: CCS Bool -> CCS Bool -> Property
prop_sim p1 p2 = forAll (simCounterexampleGen p1 p2) $ 
                 \m -> case m of 
                         Nothing -> property True
                         Just (path,p') -> collect (Just (length path)) True

prop_sim2 :: CCS Bool -> Property
prop_sim2 p = forAll (simCounterexampleGen p p) $ 
                 \m -> case m of 
                         Nothing -> property True
                         Just (path,p') -> collect (Just (length path)) True

-- can we follow a path in a process, and reach a state with the given events?

canMatch [] as p = sort (nub (map fst (step p))) == sort (nub as)
canMatch (a:as) bs p = any (canMatch as bs) [p' | (a',p') <- pe, a'==a]
  where pe = step p

-- now we can test randomly whether one process can simulate another

p ~^^~ q =
  forAll (simCounterexampleGen p q) $ \m ->
    isJust m ==> 
      let (path,p') = fromJust m in
        collect (length path) $
          looksLike $ canMatch path (map fst (step p')) q

prop_self_bisimulate (p :: CCS Bool) =
  p ~^^~ p

prop_bisimulate_alt (Shrink2 (Shrink2 (p,q)) :: Two (CCS Bool)) =
  Alt p q ~^^~ p

prop_bisimulate_alt2 (Shrink2 p :: Shrink2 (CCS Bool)) =
  p ~^^~ Alt p p

prop_bisimulate_par (p :: CCS Bool) =
  p ~^^~ Par p p

type Two a = Shrink2 (Shrink2 (a,a))

--- same properties as above, but with randomized testing

prop_random_refl (p :: CCS Bool) = p ~^~ p

prop_random_alt_nil_zero (p :: CCS Bool) = p ~^~ Alt Nil p

prop_random_alt_idempotent (p :: CCS Bool) = Alt p p ~^~ p

prop_random_alt_symmetric (p) (q) = Alt p q ~^~ Alt q p

prop_random_par_nil_zero (p :: CCS Bool) = p ~^~ Par Nil p

prop_random_par_idempotent (p :: CCS Bool) = expectFailure $ Par p p ~^~ p

prop_random_par_symmetric (p :: CCS Bool) (q :: CCS Bool) =
  Par p q ~^~ Par q p

prop_random_alt_is_not_par (p :: CCS Bool) (q :: CCS Bool) =
  Par p q ~^~ Alt p q

prop_random_three_is_not_four (p :: CCS Bool) =
  foldr1 Par [p,p,p,p] ~^~ foldr1 Par [p,p,p]

prop_random_bisimilarity a (p :: CCS Bool) (q :: CCS Bool) =
  Act a (Alt p q) ~^~ Alt (Act a p) (Act a q)

prop_random_act_par a (p :: CCS Bool) (q :: CCS Bool) =
  Par (Act a p) q ~^~ Act a (Par p q)
