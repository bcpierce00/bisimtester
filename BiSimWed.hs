{-# LANGUAGE TypeFamilies, FlexibleContexts, RankNTypes #-}

module BiSimWed where

import Test.QuickCheck
import Data.Maybe
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set( Set )
import System.Cmd
import Data.Tree
import Data.Tree.Pretty

class (Show p, Ord p) => Proc p where 
  type Event p
  step :: p -> [(Event p, p)]

(~~) :: (Proc p, Ord (Event p)) => p -> p -> Bool
p ~~ q =
  rep rel p == rep rel q
 where
  top = explore (-1) S.empty [p,q]
  rel = fix id refRel [top]    -- N.b.: not fix length!

ork = 1000

(~^~) :: (Proc p, Ord (Event p)) => p -> p -> Property
p ~^~ q
  | S.size top < ork =
      property $ rep rel p == rep rel q
  | otherwise = 
      False ==> True
 where
  top = explore ork S.empty [p,q]
  rel = fix id refRel [top]    -- N.b.: not fix length!

explore :: Proc p => Int -> Set p -> [p] -> Set p
explore 0 seen _        = seen
explore n seen []       = seen
explore n seen (p:ps)
  | p `S.member` seen = explore n seen ps
  | otherwise         = explore (n-1) (p `S.insert` seen) (map snd (step p) ++ ps)

refClass :: (Proc p, Ord (Event p)) => (p -> p) -> Set p -> [Set p]
refClass currrep ps =
  [ S.fromList qs
  | (_,qs) <- M.toList table
  ]
 where
  rep' p = map head $ group $ sort [ (e,currrep p') | (e,p') <- step p ]
  table  = M.fromListWith (++) [ (rep' p, [p]) | p <- S.toList ps ]

refRel :: (Proc p, Ord (Event p))  => [Set p] -> [Set p]
refRel pss =
  [ qs 
  | ps <- pss
  , qs <- refClass (rep pss) ps
  , S.size qs > 1
  ]

rep :: Proc p => [Set p] -> (p -> p)
rep pss p = head $
  [ S.findMin ps
  | ps <- pss
  , p `S.member` ps
  ] ++
  [ p ]  -- why is this needed? (because of the singleton-dropping optimization)

fix h f x
  | h x == h fx = x
  | otherwise   = fix h f fx 
 where
  fx = f x

-----------------------------------------------------
-- CCS (a la Koen)

data Msg
  = In Char
  | Out Char
 deriving ( Eq, Ord )

dual :: Msg -> Msg
dual (In a)  = Out a
dual (Out a) = In a

instance Show Msg where
  show (In  a) = [a,'?']
  show (Out a) = [a,'!']

instance Arbitrary Msg where
  arbitrary =
    do a <- growingElements ['a'..'h']
       b <- arbitrary
       return (if b then In a else Out a)

  shrink (In a)  = [ Out b | b <- [a,succ a] ] ++
                   [ In a'  | a' <- shrink a ]
  shrink (Out a) = [ Out a' | a' <- shrink a ]

data CCSEvent
  = Do Msg | Tau
  deriving (Eq, Ord)

instance Show CCSEvent where
  show Tau = "_."
  show (Do m) = show m  

instance Arbitrary CCSEvent where
  arbitrary = frequency [(1,return Tau),(3,arbitrary)]
  shrink Tau = []
  shrink (Do m) = Tau : map Do (shrink m)

matches Tau _ = False
matches _ Tau = False
matches (Do a) (Do b) = a == dual b

data P
  = Nil
  | Act CCSEvent P
  | P :+: P
  | P :|: P
  | Star P
 deriving ( Eq, Ord )

instance Show P where
  show Nil       = "0"
  show (Act m p) = show m ++ show p
  show (p :+: q) = "(" ++ show p ++ "+" ++ show q ++ ")"
  show (p :|: q) = "(" ++ show p ++ " | " ++ show q ++ ")"
  show (Star p)  = "(" ++ show p ++ ")*"

instance Arbitrary P where
  arbitrary = sized (arbP . (`div` 3))
   where
    arbP n =
      frequency
      [ (1, return Nil)
      , (k, do m <- arbitrary
               p <- arbP n1
               return (Act m p))
      , (k, do p <- arbP n2
               q <- arbP n2
               op <- elements [(:|:),(:+:)]
               return (p `op` q))
      , (1, do p <- arbP n1
               return (Star p))
      ]
     where
      k  = 5 `min` n
      n1 = n-1
      n2 = n `div` 2

  shrink Nil       = []
  shrink (Act m p) = [ p ] ++
                     [ Act m' p | m' <- shrink m ] ++
                     [ Act m p' | p' <- shrink p ]
  shrink (p :+: q) = [ p, q ] ++
                     [ p' :+: q | p' <- shrink p ] ++
                     [ p :+: q' | q' <- shrink q ]
  shrink (p :|: q) = [ p, q, p :+: q ] ++
                     [ p' :|: q | p' <- shrink p ] ++
                     [ p :|: q' | q' <- shrink q ]
  shrink (Star p)  = [ p ] ++ map Star (shrink p)

instance Proc P where
  type Event P = CCSEvent

  step Nil =
    []

  step (Act m p) =
    [(m, p)]

  step (p :+: q) =
    step p ++ step q

  step (p :|: q) =
    [ (Tau, p' :|: q')
    | (a, p') <- ps
    , (b, q') <- qs
    , matches a b
    ] ++
    [ (m, p' :|: q)
    | (m, p') <- ps
    ] ++
    [ (m, p :|: q')
    | (m, q') <- qs
    ]
   where
    ps = step p
    qs = step q

  step (Star p) = 
    [ (e,p' :|: Star p) | (e,p') <- ps]  ++
    [ (Tau,p' :|: q' :|: Star p) 
    | (a,p') <- ps,
      (b,q') <- ps,
      matches a b ]
    where
      ps = step p

type At p = forall a b. ((p -> a) -> b) -> (p -> a) -> b

atP :: At P
atP = id

atCCSEvent :: At Msg
atCCSEvent = id

prop_Refl p =
  p ~^~ p

prop_Plus_Nil p =
  (Nil :+: p) ~^~ p

prop_Par_Nil p =
  (Nil :|: p) ~^~ p

-- this is very slow to test!
prop_Par_commutes p q =
  (p :|: q) ~^~ (q :|: p)

prop_Par_commutes_state_space p q =
  collect (S.size $ explore (-1) S.empty [p :|: q,q :|: p]) True

prop_Par_associates p q r =
  (p :|: (q :|: r)) ~^~ ((p :|: q) :|: r)

prop_Wrong p q =
  expectFailure $
    p ~^~ q

prop_Wrong2 m p q =
  expectFailure $
    Act m (p :+: q) ~^~ (Act m p :+: Act m q)

prop_Wrong3 m p q =
  expectFailure $
    Act m (p :|: q) ~^~ (Act m p :|: Act m q)

prop_Wrong4 p q r s =
  (p :|: (q :|: (r :|: s))) ~^~ ((p :|: q) :|: r)
  
prop_Wrong5 p q r s =
  (p :|: (q :|: (r :+: s))) ~~ (p :|: ((q :|: r) :+: (q :|: s)))

prop_Wrong6 p q r =
  (p' :|: q') ~^~ (p' :|: r')
  where p' = iterate (Act (Do (Out 'a'))) p !! hard
        q' = iterate (Act (Do (In 'a')) Nil :|:) q !! hard
        r' = iterate (Act (Do (In 'a')) Nil :|:) r !! hard
        hard = 10

runPTests = do
    atP qc prop_Refl
    qc prop_Plus_Nil
    qc prop_Par_Nil
    qc prop_Par_commutes
--    qc prop_Par_commutes_state_space
    qc prop_Par_associates
    atP qc prop_Wrong
    qc prop_Wrong2
    qc prop_Wrong3

qc :: Testable a => a -> IO ()
qc = quickCheckWith stdArgs{maxSuccess=1000}


--- normalization of P

norm :: Int -> P -> P
norm 0 _ = Nil
norm n p 
  | null ps = Nil
  | otherwise = 
      foldr1 (:+:) (map head . group . sort $ 
                    [Act m (norm (n-1) q) | (m,q) <- ps])
  where ps = step p

prop_norm p q =
  (p ~~ q) == (norm (-1) p == norm (-1) q)

prop_norm_implies_bisim p q =
  norm 12 p == norm 12 q ==> p ~^~ q

{-

Experiments show that normalizing a process is too expensive. We
reasoned that, if we represent equivalence classes with unknown
members, then we must characterize the behaviour of those unknown
members with something equivalent to a
normalization-up-to-a-fixed-depth of the processes. This suggests that
using an exact equivalence relation is going to be too expensive.

So... suppose we do weaken the requirement that we are working with an
equivalence relation. An ER gives us a partition of the state space,
but suppose we settled for a covering of the state space instead? Then
when comparing two states, we would have ask not "do they have the
same representative", but "is there a set in the covering containing
both"? This is more expensive, but not catastrophically so... and we
hope may let us work with a restricted subset of the state space. The
next thing to try.

Additional thoughts (19/9): normalizing by floating Alts to the top is
stupid: we know Par will blow up that way. Can we "normalize" by
keeping Par at the top instead? We wouldn't get unique normal forms,
but maybe we can cope with that. The idea is to represent a set of
"non racing" events that a process can do in any order.

  -}

data LTS = N [(CCSEvent,LTS)]
  deriving Show

unfold p = N $ [(e,unfold p') | (e,p') <- step p]

prune 0 (N eps) = N []
prune d (N eps) = N [(e,prune (if e==Tau then d else d-1) p') | (e,p')<-eps]

blur t = blur' t
  where blur' 0 (N eps) = N []
        blur' t' (N eps) = N [(e,blur' (if e==Tau then (t'-1) else t) p') | (e,p') <- eps]

tree d t p = prune d $ blur t $ unfold p

drawAct Tau = "tau"
drawAct (Do (Out a)) = a : "!"
drawAct (Do (In a)) = a : "?"

treeOf = treeOf' ""
  where treeOf' l (N eps) = Node l [ treeOf' (drawAct e') p' | (e',p') <- eps ] 

draw d t p = putStr $ drawTree $ treeOf $ tree d t p

p1 = (Act Tau (Act Tau Nil))
p2 = Star (Act Tau (Act (Do (Out 'a')) Nil))
p3 = Star (Act Tau (Act Tau (Act (Do (Out 'a')) Nil)))

-- draw trees

dot t = do
  writeFile "tree.dot" $
    "digraph{\n"++dot' 1 t++"}\n"
  system "dot -Tjpg -O tree.dot"
  system "tree.dot.jpg"

dot' _ t = "node [];\n"

