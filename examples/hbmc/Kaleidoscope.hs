{-# LANGUAGE OverlappingInstances,FlexibleInstances #-}
module Kaleidoscope where

import HipSpec
import Prelude hiding ((++))

data Token
    = Butterfly
    | I
    | In
    | Me
    | Kaleidoscope
    | Saw
    | The
  deriving Show

data S = S NP VP
  deriving Show

data Case = Subj | Obj

linS :: S -> [Token]
linS (S np vp) = linNP Subj np ++ linVP vp

data NP = Pron1 | Det N | NP `NP_In` NP
  deriving Show

linNP :: Case -> NP -> [Token]
linNP Subj Pron1   = [I]
linNP Obj  Pron1   = [Me] -- myself?
linNP _    (Det n) = [The] ++ linN n
linNP c (NP_In np1 np2) = linNP c np1 ++ [In] ++ linNP c np2

data N = N_Butterfly | N_Kaleidoscope
  deriving Show

linN :: N -> [Token]
linN N_Butterfly    = [Butterfly]
linN N_Kaleidoscope = [Kaleidoscope]

data VP = See NP | VP `VP_In` NP
  deriving Show

linVP :: VP -> [Token]
linVP (See np) = [Saw] ++ linNP Obj np
linVP (VP_In vp np) = linVP vp ++ [In] ++ linNP Obj np

-- examples --

ex1_parsing s = linS s =/= [I,Saw,The,Butterfly,In,The,Kaleidoscope]

ex2_two_parses t1 t2 =
        linS t1 =:= [I,Saw,The,Butterfly,In,The,Kaleidoscope]
     /\ linS t2 =:= [I,Saw,The,Butterfly,In,The,Kaleidoscope]
    ==> t1 =:= t2

ex3_ambiguity t1 t2 = linS t1 =:= linS t2 ==> t1 =:= t2

-- append --

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

-- showing --

instance Show (S,S) where
  show (s1,s2) = show s1 ++ "\n" ++ show s2 ++ "\n" ++ show (linS s1)

