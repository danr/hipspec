{-# LANGUAGE TypeFamilies,GeneralizedNewtypeDeriving,NoMonomorphismRestriction #-}
module Main where
import qualified Symbolic
import qualified Prelude
import Prelude (Bool(..),(=<<))
import Definitions
import TurboSpec
import Symbolic (equal,escapeH,Lift(..),nt)
import Prelude (return,sequence,($))
data Label_Bool =
  Label_False | Label_True
    deriving (Prelude.Ord,Prelude.Eq,Prelude.Show)
newtype D_Bool =
  D_Bool (Symbolic.Data Label_Bool ())
    deriving (Prelude.Show,Symbolic.Choice,Symbolic.Equal)
con_False = D_Bool (Symbolic.Con (Symbolic.val Label_False) ())
con_True = D_Bool (Symbolic.Con (Symbolic.val Label_True) ())
data Label__rbrack__lbrack_ =
  Label__rbrack__lbrack_ | Label__cons_
    deriving (Prelude.Ord,Prelude.Eq,Prelude.Show)
newtype D__rbrack__lbrack_ a =
  D__rbrack__lbrack_
    (Symbolic.Data
       Label__rbrack__lbrack_
       ((,) (Symbolic.Lift a) (Symbolic.Lift (D__rbrack__lbrack_ a))))
    deriving (Prelude.Show,Symbolic.Choice,Symbolic.Equal)
con__rbrack__lbrack_ =
  D__rbrack__lbrack_
    (Symbolic.Con
       (Symbolic.val Label__rbrack__lbrack_)
       ((,) Symbolic.UNR Symbolic.UNR))
con__cons_ =
  \ con__cons_0 con__cons_1 ->
    D__rbrack__lbrack_
      (Symbolic.Con
         (Symbolic.val Label__cons_)
         ((,) (Symbolic.The con__cons_0) (Symbolic.The con__cons_1)))
data Label_Nat =
  Label_S | Label_Z deriving (Prelude.Ord,Prelude.Eq,Prelude.Show)
newtype D_Nat =
  D_Nat
    (Symbolic.Data Label_Nat (Symbolic.One (Symbolic.Lift D_Nat)))
    deriving (Prelude.Show,Symbolic.Choice,Symbolic.Equal)
con_S =
  \ con_S0 ->
    D_Nat
      (Symbolic.Con
         (Symbolic.val Label_S) (Symbolic.One (Symbolic.The con_S0)))
con_Z =
  D_Nat
    (Symbolic.Con (Symbolic.val Label_Z) (Symbolic.One Symbolic.UNR))
instance Symbolic.Value D_Bool where
  type Type D_Bool = Bool
  get =
    \ tmp0 ->
      case tmp0 of
        { D_Bool tmp1 ->
            case tmp1 of
              { Symbolic.Con cn2 args3 ->
                  Symbolic.get cn2 Prelude.>>= \ lbl4 ->
                  (case args3 of
                     { () ->
                         case lbl4 of
                           { Label_False -> Prelude.return False
                           ; Label_True -> Prelude.return True
                           }
                     })
              }
        }
instance (Symbolic.Value a) =>
  Symbolic.Value (D__rbrack__lbrack_ a)
  where
  type Type (D__rbrack__lbrack_ a) = [] (Symbolic.Type a)
  get =
    \ tmp5 ->
      case tmp5 of
        { D__rbrack__lbrack_ tmp6 ->
            case tmp6 of
              { Symbolic.Con cn7 args8 ->
                  Symbolic.get cn7 Prelude.>>= \ lbl9 ->
                  (case args8 of
                     { (,) arg16 arg17 ->
                         case lbl9 of
                           { Label__rbrack__lbrack_ -> Prelude.return ([])
                           ; Label__cons_ ->
                               Symbolic.peek arg17 Prelude.>>= \ v13 ->
                               Symbolic.peek arg16 Prelude.>>= \ v12 ->
                               Symbolic.get v13 Prelude.>>= \ z15 ->
                               Symbolic.get v12 Prelude.>>= \ z14 -> Prelude.return (z14 : z15)
                           }
                     })
              }
        }
instance Symbolic.Value D_Nat where
  type Type D_Nat = Nat
  get =
    \ tmp18 ->
      case tmp18 of
        { D_Nat tmp19 ->
            case tmp19 of
              { Symbolic.Con cn20 args21 ->
                  Symbolic.get cn20 Prelude.>>= \ lbl22 ->
                  (case args21 of
                     { Symbolic.One arg26 ->
                         case lbl22 of
                           { Label_S ->
                               Symbolic.peek arg26 Prelude.>>= \ v23 ->
                               Symbolic.get v23 Prelude.>>= \ z24 -> Prelude.return (S z24)
                           ; Label_Z -> Prelude.return Z
                           }
                     })
              }
        }
instance Symbolic.Argument Label_Bool where
  argument =
    \ lbl27 tuple28 ->
      case tuple28 of
        { Symbolic.Tuple list29 ->
            case list29 of
              { ([]) -> case lbl27 of { Label_False -> ([]); Label_True -> ([])}
              ; (:) _ _ -> Prelude.undefined
              }
        }
instance Symbolic.Argument Label__rbrack__lbrack_ where
  argument =
    \ lbl30 tuple31 ->
      case tuple31 of
        { Symbolic.Tuple list32 ->
            case list32 of
              { (:) arg33 tl35 ->
                  case tl35 of
                    { (:) arg34 tl36 ->
                        case tl36 of
                          { ([]) ->
                              case lbl30 of
                                { Label__rbrack__lbrack_ -> ([])
                                ; Label__cons_ -> arg33 : (arg34 : ([]))
                                }
                          ; (:) _ _ -> Prelude.undefined
                          }
                    ; ([]) -> Prelude.undefined
                    }
              ; ([]) -> Prelude.undefined
              }
        }
instance Symbolic.Argument Label_Nat where
  argument =
    \ lbl37 tuple38 ->
      case tuple38 of
        { Symbolic.Tuple list39 ->
            case list39 of
              { (:) arg40 tl41 ->
                  case tl41 of
                    { ([]) -> case lbl37 of { Label_S -> arg40 : ([]); Label_Z -> ([])}
                    ; (:) _ _ -> Prelude.undefined
                    }
              ; ([]) -> Prelude.undefined
              }
        }
new_Bool =
  \ s42 ->
    Symbolic.newVal
      ((Label_False : ([])) Prelude.++ (Label_True : ([])))
      Prelude.>>= \ cn43 ->
    Prelude.return (D_Bool (Symbolic.Con cn43 ()))
new__rbrack__lbrack_ =
  \ s44 mk45 ->
    Symbolic.newVal
      ((Label__rbrack__lbrack_ : ([])) Prelude.++
       (case s44 Prelude./= 0 of
          { True -> Label__cons_ : ([]); False -> ([])}))
      Prelude.>>= \ cn46 ->
    Symbolic.bara
      (s44 Prelude./= 0) (new__rbrack__lbrack_ (Prelude.pred s44) mk45)
      Prelude.>>= \ r48 ->
    Prelude.fmap Symbolic.The mk45 Prelude.>>= \ r47 ->
    Prelude.return
      (D__rbrack__lbrack_ (Symbolic.Con cn46 ((,) r47 r48)))
new_Nat =
  \ s49 ->
    Symbolic.newVal
      ((case s49 Prelude./= 0 of
          { True -> Label_S : ([]); False -> ([])})
         Prelude.++
       (Label_Z : ([])))
      Prelude.>>= \ cn50 ->
    Symbolic.bara (s49 Prelude./= 0) (new_Nat (Prelude.pred s49))
      Prelude.>>= \ r51 ->
    Prelude.return (D_Nat (Symbolic.Con cn50 (Symbolic.One r51)))
hbmc__pipe__pipe_ =
  \ ds x ->
    case ds of
      { D_Bool tmp55 ->
          Symbolic.switch
            tmp55
            (\ lbl53 args54 ->
               case args54 of
                 { () ->
                     case lbl53 of
                       { Label_False -> Prelude.return x
                       ; Label_True -> Prelude.return con_True
                       }
                 })
      }
hbmc_union =
  \ ds ys ->
    case ds of
      { D__rbrack__lbrack_ tmp104 ->
          Symbolic.switch
            tmp104
            (\ lbl100 args101 ->
               case args101 of
                 { (,) arg102 arg103 ->
                     case lbl100 of
                       { Label__rbrack__lbrack_ -> Prelude.return ys
                       ; Label__cons_ ->
                           Symbolic.peek arg103 Prelude.>>= \ xs ->
                           Symbolic.peek arg102 Prelude.>>= \ x ->
                           hbmc_elem x ys Prelude.>>= \ caser56 ->
                           Prelude.return (Symbolic.The ((,) xs ys)) Prelude.>>= \ arg57 ->
                           Symbolic.peek arg57 Prelude.>>= \ tmp94 ->
                           Symbolic.peek arg57 Prelude.>>= \ tmp95 ->
                           hbmc_union (Prelude.fst tmp94) (Prelude.snd tmp95)
                             Prelude.>>= \ tmp96 ->
                           Prelude.return (Symbolic.The tmp96) Prelude.>>= \ res58 ->
                           (case caser56 of
                              { D_Bool tmp99 ->
                                  Symbolic.switch
                                    tmp99
                                    (\ lbl97 args98 ->
                                       case args98 of
                                         { () ->
                                             case lbl97 of
                                               { Label_False ->
                                                   Symbolic.peek res58 Prelude.>>= \ tmp91 ->
                                                   Prelude.return (con__cons_ x tmp91)
                                               ; Label_True -> Symbolic.peek res58
                                               }
                                         })
                              })
                       }
                 })
      }
hbmc_subset =
  \ ds ys ->
    case ds of
      { D__rbrack__lbrack_ tmp146 ->
          Symbolic.switch
            tmp146
            (\ lbl142 args143 ->
               case args143 of
                 { (,) arg144 arg145 ->
                     case lbl142 of
                       { Label__rbrack__lbrack_ -> Prelude.return con_True
                       ; Label__cons_ ->
                           Symbolic.peek arg145 Prelude.>>= \ xs ->
                           Symbolic.peek arg144 Prelude.>>= \ x ->
                           Prelude.return (Symbolic.The ((,) xs ys)) Prelude.>>= \ arg105 ->
                           Symbolic.peek arg105 Prelude.>>= \ tmp139 ->
                           Symbolic.peek arg105 Prelude.>>= \ tmp140 ->
                           hbmc_subset (Prelude.fst tmp139) (Prelude.snd tmp140)
                             Prelude.>>= \ tmp141 ->
                           hbmc_elem x ys Prelude.>>= \ tmp135 ->
                           (Symbolic.peek (Symbolic.The tmp141)) Prelude.>>=
                           (hbmc__and__and_ tmp135)
                       }
                 })
      }
hbmc_sorted =
  \ ds ->
    case ds of
      { D__rbrack__lbrack_ tmp188 ->
          Symbolic.switch
            tmp188
            (\ lbl184 args185 ->
               case args185 of
                 { (,) arg186 arg187 ->
                     case lbl184 of
                       { Label__rbrack__lbrack_ -> Prelude.return con_True
                       ; Label__cons_ ->
                           Symbolic.peek arg187 Prelude.>>= \ ds149 ->
                           Symbolic.peek arg186 Prelude.>>= \ x ->
                           (case ds149 of
                              { D__rbrack__lbrack_ tmp183 ->
                                  Symbolic.switch
                                    tmp183
                                    (\ lbl179 args180 ->
                                       case args180 of
                                         { (,) arg181 arg182 ->
                                             case lbl179 of
                                               { Label__rbrack__lbrack_ -> Prelude.return con_True
                                               ; Label__cons_ ->
                                                   Symbolic.peek arg182 Prelude.>>= \ xs ->
                                                   Symbolic.peek arg181 Prelude.>>= \ y ->
                                                   Symbolic.peek
                                                     (Symbolic.The (Symbolic.One (con__cons_ y xs)))
                                                     Prelude.>>= \ tmp177 ->
                                                   hbmc_sorted (Symbolic.one tmp177)
                                                     Prelude.>>= \ tmp178 ->
                                                   hbmc__lt__equal_ x y Prelude.>>= \ tmp173 ->
                                                   (Symbolic.peek (Symbolic.The tmp178)) Prelude.>>=
                                                   (hbmc__and__and_ tmp173)
                                               }
                                         })
                              })
                       }
                 })
      }
hbmc_rotate =
  \ ds xs ->
    case ds of
      { D_Nat tmp242 ->
          Symbolic.switch
            tmp242
            (\ lbl239 args240 ->
               case args240 of
                 { Symbolic.One arg241 ->
                     case lbl239 of
                       { Label_S ->
                           Symbolic.peek arg241 Prelude.>>= \ d ->
                           (case xs of
                              { D__rbrack__lbrack_ tmp238 ->
                                  Symbolic.switch
                                    tmp238
                                    (\ lbl234 args235 ->
                                       case args235 of
                                         { (,) arg236 arg237 ->
                                             case lbl234 of
                                               { Label__rbrack__lbrack_ ->
                                                   Prelude.return con__rbrack__lbrack_
                                               ; Label__cons_ ->
                                                   Symbolic.peek arg237 Prelude.>>= \ d195 ->
                                                   Symbolic.peek arg236 Prelude.>>= \ d194 ->
                                                   hbmc__plus__plus_
                                                     d195 (con__cons_ d194 con__rbrack__lbrack_)
                                                     Prelude.>>= \ tmp233 ->
                                                   Prelude.return (Symbolic.The ((,) d tmp233))
                                                     Prelude.>>= \ arg189 ->
                                                   Symbolic.peek arg189 Prelude.>>= \ tmp230 ->
                                                   Symbolic.peek arg189 Prelude.>>= \ tmp231 ->
                                                   hbmc_rotate
                                                     (Prelude.fst tmp230) (Prelude.snd tmp231)
                                                     Prelude.>>= \ tmp232 ->
                                                   Symbolic.peek (Symbolic.The tmp232)
                                               }
                                         })
                              })
                       ; Label_Z -> Prelude.return xs
                       }
                 })
      }
hbmc_revflat =
  \ ds ->
    case ds of
      { D__rbrack__lbrack_ tmp274 ->
          Symbolic.switch
            tmp274
            (\ lbl270 args271 ->
               case args271 of
                 { (,) arg272 arg273 ->
                     case lbl270 of
                       { Label__rbrack__lbrack_ -> Prelude.return con__rbrack__lbrack_
                       ; Label__cons_ ->
                           Symbolic.peek arg273 Prelude.>>= \ xss ->
                           Symbolic.peek arg272 Prelude.>>= \ xs ->
                           Symbolic.peek (Symbolic.The (Symbolic.One xss))
                             Prelude.>>= \ tmp268 ->
                           hbmc_revflat (Symbolic.one tmp268) Prelude.>>= \ tmp269 ->
                           Symbolic.peek (Symbolic.The tmp269) Prelude.>>= \ tmp266 ->
                           hbmc__plus__plus_ tmp266 xs
                       }
                 })
      }
hbmc_rev =
  \ ds ->
    case ds of
      { D__rbrack__lbrack_ tmp309 ->
          Symbolic.switch
            tmp309
            (\ lbl305 args306 ->
               case args306 of
                 { (,) arg307 arg308 ->
                     case lbl305 of
                       { Label__rbrack__lbrack_ -> Prelude.return con__rbrack__lbrack_
                       ; Label__cons_ ->
                           Symbolic.peek arg308 Prelude.>>= \ xs ->
                           Symbolic.peek arg307 Prelude.>>= \ x ->
                           Symbolic.peek (Symbolic.The (Symbolic.One xs))
                             Prelude.>>= \ tmp303 ->
                           hbmc_rev (Symbolic.one tmp303) Prelude.>>= \ tmp304 ->
                           Symbolic.peek (Symbolic.The tmp304) Prelude.>>= \ tmp298 ->
                           hbmc__plus__plus_ tmp298 (con__cons_ x con__rbrack__lbrack_)
                       }
                 })
      }
hbmc_qrevflat =
  \ ds acc ->
    case ds of
      { D__rbrack__lbrack_ tmp359 ->
          Symbolic.switch
            tmp359
            (\ lbl355 args356 ->
               case args356 of
                 { (,) arg357 arg358 ->
                     case lbl355 of
                       { Label__rbrack__lbrack_ -> Prelude.return acc
                       ; Label__cons_ ->
                           Symbolic.peek arg358 Prelude.>>= \ xss ->
                           Symbolic.peek arg357 Prelude.>>= \ xs ->
                           hbmc_rev xs Prelude.>>= \ tmp353 ->
                           hbmc__plus__plus_ tmp353 acc Prelude.>>= \ tmp354 ->
                           Prelude.return (Symbolic.The ((,) xss tmp354))
                             Prelude.>>= \ arg310 ->
                           Symbolic.peek arg310 Prelude.>>= \ tmp350 ->
                           Symbolic.peek arg310 Prelude.>>= \ tmp351 ->
                           hbmc_qrevflat (Prelude.fst tmp350) (Prelude.snd tmp351)
                             Prelude.>>= \ tmp352 ->
                           Symbolic.peek (Symbolic.The tmp352)
                       }
                 })
      }
hbmc_qrev =
  \ ds acc ->
    case ds of
      { D__rbrack__lbrack_ tmp400 ->
          Symbolic.switch
            tmp400
            (\ lbl396 args397 ->
               case args397 of
                 { (,) arg398 arg399 ->
                     case lbl396 of
                       { Label__rbrack__lbrack_ -> Prelude.return acc
                       ; Label__cons_ ->
                           Symbolic.peek arg399 Prelude.>>= \ xs ->
                           Symbolic.peek arg398 Prelude.>>= \ x ->
                           Prelude.return (Symbolic.The ((,) xs (con__cons_ x acc)))
                             Prelude.>>= \ arg360 ->
                           Symbolic.peek arg360 Prelude.>>= \ tmp393 ->
                           Symbolic.peek arg360 Prelude.>>= \ tmp394 ->
                           hbmc_qrev (Prelude.fst tmp393) (Prelude.snd tmp394)
                             Prelude.>>= \ tmp395 ->
                           Symbolic.peek (Symbolic.The tmp395)
                       }
                 })
      }
hbmc_mult =
  \ ds ds403 acc ->
    case ds of
      { D_Nat tmp451 ->
          Symbolic.switch
            tmp451
            (\ lbl448 args449 ->
               case args449 of
                 { Symbolic.One arg450 ->
                     case lbl448 of
                       { Label_S ->
                           Symbolic.peek arg450 Prelude.>>= \ x ->
                           hbmc__plus_ ds403 acc Prelude.>>= \ tmp447 ->
                           Prelude.return (Symbolic.The ((,,) x ds403 tmp447))
                             Prelude.>>= \ arg401 ->
                           Symbolic.peek arg401 Prelude.>>= \ tmp443 ->
                           Symbolic.peek arg401 Prelude.>>= \ tmp444 ->
                           Symbolic.peek arg401 Prelude.>>= \ tmp445 ->
                           hbmc_mult
                             (Symbolic.proj0_3 tmp443)
                             (Symbolic.proj1_3 tmp444)
                             (Symbolic.proj2_3 tmp445)
                             Prelude.>>= \ tmp446 ->
                           Symbolic.peek (Symbolic.The tmp446)
                       ; Label_Z -> Prelude.return acc
                       }
                 })
      }
hbmc_length =
  \ ds ->
    case ds of
      { D__rbrack__lbrack_ tmp482 ->
          Symbolic.switch
            tmp482
            (\ lbl478 args479 ->
               case args479 of
                 { (,) arg480 arg481 ->
                     case lbl478 of
                       { Label__rbrack__lbrack_ -> Prelude.return con_Z
                       ; Label__cons_ ->
                           Symbolic.peek arg481 Prelude.>>= \ xs ->
                           Symbolic.peek arg480 Prelude.>>= \ ds456 ->
                           Symbolic.peek (Symbolic.The (Symbolic.One xs))
                             Prelude.>>= \ tmp476 ->
                           hbmc_length (Symbolic.one tmp476) Prelude.>>= \ tmp477 ->
                           Symbolic.peek (Symbolic.The tmp477) Prelude.>>= \ tmp475 ->
                           Prelude.return (con_S tmp475)
                       }
                 })
      }
hbmc_isort =
  \ ds ->
    case ds of
      { D__rbrack__lbrack_ tmp511 ->
          Symbolic.switch
            tmp511
            (\ lbl507 args508 ->
               case args508 of
                 { (,) arg509 arg510 ->
                     case lbl507 of
                       { Label__rbrack__lbrack_ -> Prelude.return con__rbrack__lbrack_
                       ; Label__cons_ ->
                           Symbolic.peek arg510 Prelude.>>= \ xs ->
                           Symbolic.peek arg509 Prelude.>>= \ x ->
                           Symbolic.peek (Symbolic.The (Symbolic.One xs))
                             Prelude.>>= \ tmp505 ->
                           hbmc_isort (Symbolic.one tmp505) Prelude.>>= \ tmp506 ->
                           (Symbolic.peek (Symbolic.The tmp506)) Prelude.>>= (hbmc_insert x)
                       }
                 })
      }
hbmc_intersect =
  \ ds ys ->
    case ds of
      { D__rbrack__lbrack_ tmp560 ->
          Symbolic.switch
            tmp560
            (\ lbl556 args557 ->
               case args557 of
                 { (,) arg558 arg559 ->
                     case lbl556 of
                       { Label__rbrack__lbrack_ -> Prelude.return con__rbrack__lbrack_
                       ; Label__cons_ ->
                           Symbolic.peek arg559 Prelude.>>= \ xs ->
                           Symbolic.peek arg558 Prelude.>>= \ x ->
                           hbmc_elem x ys Prelude.>>= \ caser512 ->
                           Prelude.return (Symbolic.The ((,) xs ys)) Prelude.>>= \ arg513 ->
                           Symbolic.peek arg513 Prelude.>>= \ tmp550 ->
                           Symbolic.peek arg513 Prelude.>>= \ tmp551 ->
                           hbmc_intersect (Prelude.fst tmp550) (Prelude.snd tmp551)
                             Prelude.>>= \ tmp552 ->
                           Prelude.return (Symbolic.The tmp552) Prelude.>>= \ res514 ->
                           (case caser512 of
                              { D_Bool tmp555 ->
                                  Symbolic.switch
                                    tmp555
                                    (\ lbl553 args554 ->
                                       case args554 of
                                         { () ->
                                             case lbl553 of
                                               { Label_False -> Symbolic.peek res514
                                               ; Label_True ->
                                                   Symbolic.peek res514 Prelude.>>= \ tmp549 ->
                                                   Prelude.return (con__cons_ x tmp549)
                                               }
                                         })
                              })
                       }
                 })
      }
hbmc_insert =
  \ n ds ->
    case ds of
      { D__rbrack__lbrack_ tmp616 ->
          Symbolic.switch
            tmp616
            (\ lbl612 args613 ->
               case args613 of
                 { (,) arg614 arg615 ->
                     case lbl612 of
                       { Label__rbrack__lbrack_ ->
                           Prelude.return (con__cons_ n con__rbrack__lbrack_)
                       ; Label__cons_ ->
                           Symbolic.peek arg615 Prelude.>>= \ xs ->
                           Symbolic.peek arg614 Prelude.>>= \ x ->
                           hbmc__lt__equal_ n x Prelude.>>= \ caser561 ->
                           (case caser561 of
                              { D_Bool tmp611 ->
                                  Symbolic.switch
                                    tmp611
                                    (\ lbl609 args610 ->
                                       case args610 of
                                         { () ->
                                             case lbl609 of
                                               { Label_False ->
                                                   Prelude.return (Symbolic.The ((,) n xs))
                                                     Prelude.>>= \ arg562 ->
                                                   Symbolic.peek arg562 Prelude.>>= \ tmp600 ->
                                                   Symbolic.peek arg562 Prelude.>>= \ tmp601 ->
                                                   hbmc_insert
                                                     (Prelude.fst tmp600) (Prelude.snd tmp601)
                                                     Prelude.>>= \ tmp602 ->
                                                   Symbolic.peek (Symbolic.The tmp602)
                                                     Prelude.>>= \ tmp599 ->
                                                   Prelude.return (con__cons_ x tmp599)
                                               ; Label_True ->
                                                   Prelude.return (con__cons_ n (con__cons_ x xs))
                                               }
                                         })
                              })
                       }
                 })
      }
hbmc_half =
  \ ds ->
    case ds of
      { D_Nat tmp649 ->
          Symbolic.switch
            tmp649
            (\ lbl646 args647 ->
               case args647 of
                 { Symbolic.One arg648 ->
                     case lbl646 of
                       { Label_S ->
                           Symbolic.peek arg648 Prelude.>>= \ ds619 ->
                           (case ds619 of
                              { D_Nat tmp645 ->
                                  Symbolic.switch
                                    tmp645
                                    (\ lbl642 args643 ->
                                       case args643 of
                                         { Symbolic.One arg644 ->
                                             case lbl642 of
                                               { Label_S ->
                                                   Symbolic.peek arg644 Prelude.>>= \ x ->
                                                   Symbolic.peek (Symbolic.The (Symbolic.One x))
                                                     Prelude.>>= \ tmp640 ->
                                                   hbmc_half (Symbolic.one tmp640)
                                                     Prelude.>>= \ tmp641 ->
                                                   Symbolic.peek (Symbolic.The tmp641)
                                                     Prelude.>>= \ tmp639 ->
                                                   Prelude.return (con_S tmp639)
                                               ; Label_Z -> Prelude.return con_Z
                                               }
                                         })
                              })
                       ; Label_Z -> Prelude.return con_Z
                       }
                 })
      }
hbmc_even =
  \ ds ->
    case ds of
      { D_Nat tmp680 ->
          Symbolic.switch
            tmp680
            (\ lbl677 args678 ->
               case args678 of
                 { Symbolic.One arg679 ->
                     case lbl677 of
                       { Label_S ->
                           Symbolic.peek arg679 Prelude.>>= \ ds652 ->
                           (case ds652 of
                              { D_Nat tmp676 ->
                                  Symbolic.switch
                                    tmp676
                                    (\ lbl673 args674 ->
                                       case args674 of
                                         { Symbolic.One arg675 ->
                                             case lbl673 of
                                               { Label_S ->
                                                   Symbolic.peek arg675 Prelude.>>= \ x ->
                                                   Symbolic.peek (Symbolic.The (Symbolic.One x))
                                                     Prelude.>>= \ tmp671 ->
                                                   hbmc_even (Symbolic.one tmp671)
                                                     Prelude.>>= \ tmp672 ->
                                                   Symbolic.peek (Symbolic.The tmp672)
                                               ; Label_Z -> Prelude.return con_False
                                               }
                                         })
                              })
                       ; Label_Z -> Prelude.return con_True
                       }
                 })
      }
hbmc_elem =
  \ ds ds683 ->
    case ds683 of
      { D__rbrack__lbrack_ tmp723 ->
          Symbolic.switch
            tmp723
            (\ lbl719 args720 ->
               case args720 of
                 { (,) arg721 arg722 ->
                     case lbl719 of
                       { Label__rbrack__lbrack_ -> Prelude.return con_False
                       ; Label__cons_ ->
                           Symbolic.peek arg722 Prelude.>>= \ xs ->
                           Symbolic.peek arg721 Prelude.>>= \ x ->
                           Prelude.return (Symbolic.The ((,) ds xs)) Prelude.>>= \ arg681 ->
                           Symbolic.peek arg681 Prelude.>>= \ tmp716 ->
                           Symbolic.peek arg681 Prelude.>>= \ tmp717 ->
                           hbmc_elem (Prelude.fst tmp716) (Prelude.snd tmp717)
                             Prelude.>>= \ tmp718 ->
                           hbmc__equal__equal_ ds x Prelude.>>= \ tmp712 ->
                           (Symbolic.peek (Symbolic.The tmp718)) Prelude.>>=
                           (hbmc__pipe__pipe_ tmp712)
                       }
                 })
      }
hbmc_drop =
  \ ds xs ->
    case ds of
      { D_Nat tmp768 ->
          Symbolic.switch
            tmp768
            (\ lbl765 args766 ->
               case args766 of
                 { Symbolic.One arg767 ->
                     case lbl765 of
                       { Label_S ->
                           Symbolic.peek arg767 Prelude.>>= \ d ->
                           (case xs of
                              { D__rbrack__lbrack_ tmp764 ->
                                  Symbolic.switch
                                    tmp764
                                    (\ lbl760 args761 ->
                                       case args761 of
                                         { (,) arg762 arg763 ->
                                             case lbl760 of
                                               { Label__rbrack__lbrack_ ->
                                                   Prelude.return con__rbrack__lbrack_
                                               ; Label__cons_ ->
                                                   Symbolic.peek arg763 Prelude.>>= \ d729 ->
                                                   Symbolic.peek arg762 Prelude.>>= \ d728 ->
                                                   Prelude.return (Symbolic.The ((,) d d729))
                                                     Prelude.>>= \ arg724 ->
                                                   Symbolic.peek arg724 Prelude.>>= \ tmp757 ->
                                                   Symbolic.peek arg724 Prelude.>>= \ tmp758 ->
                                                   hbmc_drop
                                                     (Prelude.fst tmp757) (Prelude.snd tmp758)
                                                     Prelude.>>= \ tmp759 ->
                                                   Symbolic.peek (Symbolic.The tmp759)
                                               }
                                         })
                              })
                       ; Label_Z -> Prelude.return xs
                       }
                 })
      }
hbmc_double =
  \ ds ->
    case ds of
      { D_Nat tmp798 ->
          Symbolic.switch
            tmp798
            (\ lbl795 args796 ->
               case args796 of
                 { Symbolic.One arg797 ->
                     case lbl795 of
                       { Label_S ->
                           Symbolic.peek arg797 Prelude.>>= \ x ->
                           Symbolic.peek (Symbolic.The (Symbolic.One x))
                             Prelude.>>= \ tmp793 ->
                           hbmc_double (Symbolic.one tmp793) Prelude.>>= \ tmp794 ->
                           Symbolic.peek (Symbolic.The tmp794) Prelude.>>= \ tmp792 ->
                           Prelude.return (con_S (con_S tmp792))
                       ; Label_Z -> Prelude.return con_Z
                       }
                 })
      }
hbmc_count =
  \ n ds ->
    case ds of
      { D__rbrack__lbrack_ tmp846 ->
          Symbolic.switch
            tmp846
            (\ lbl842 args843 ->
               case args843 of
                 { (,) arg844 arg845 ->
                     case lbl842 of
                       { Label__rbrack__lbrack_ -> Prelude.return con_Z
                       ; Label__cons_ ->
                           Symbolic.peek arg845 Prelude.>>= \ xs ->
                           Symbolic.peek arg844 Prelude.>>= \ x ->
                           hbmc__equal__equal_ n x Prelude.>>= \ caser799 ->
                           Prelude.return (Symbolic.The ((,) n xs)) Prelude.>>= \ arg800 ->
                           Symbolic.peek arg800 Prelude.>>= \ tmp836 ->
                           Symbolic.peek arg800 Prelude.>>= \ tmp837 ->
                           hbmc_count (Prelude.fst tmp836) (Prelude.snd tmp837)
                             Prelude.>>= \ tmp838 ->
                           Prelude.return (Symbolic.The tmp838) Prelude.>>= \ res801 ->
                           (case caser799 of
                              { D_Bool tmp841 ->
                                  Symbolic.switch
                                    tmp841
                                    (\ lbl839 args840 ->
                                       case args840 of
                                         { () ->
                                             case lbl839 of
                                               { Label_False -> Symbolic.peek res801
                                               ; Label_True ->
                                                   Symbolic.peek res801 Prelude.>>= \ tmp835 ->
                                                   Prelude.return (con_S tmp835)
                                               }
                                         })
                              })
                       }
                 })
      }
hbmc__equal__equal_ =
  \ ds ds849 ->
    case ds of
      { D_Nat tmp893 ->
          Symbolic.switch
            tmp893
            (\ lbl890 args891 ->
               case args891 of
                 { Symbolic.One arg892 ->
                     case lbl890 of
                       { Label_S ->
                           Symbolic.peek arg892 Prelude.>>= \ ds850 ->
                           (case ds849 of
                              { D_Nat tmp885 ->
                                  Symbolic.switch
                                    tmp885
                                    (\ lbl882 args883 ->
                                       case args883 of
                                         { Symbolic.One arg884 ->
                                             case lbl882 of
                                               { Label_S ->
                                                   Symbolic.peek arg884 Prelude.>>= \ y ->
                                                   Prelude.return (Symbolic.The ((,) ds850 y))
                                                     Prelude.>>= \ arg847 ->
                                                   Symbolic.peek arg847 Prelude.>>= \ tmp878 ->
                                                   Symbolic.peek arg847 Prelude.>>= \ tmp879 ->
                                                   hbmc__equal__equal_
                                                     (Prelude.fst tmp878) (Prelude.snd tmp879)
                                                     Prelude.>>= \ tmp880 ->
                                                   Symbolic.peek (Symbolic.The tmp880)
                                               ; Label_Z -> Prelude.return con_False
                                               }
                                         })
                              })
                       ; Label_Z ->
                           case ds849 of
                             { D_Nat tmp889 ->
                                 Symbolic.switch
                                   tmp889
                                   (\ lbl886 args887 ->
                                      case args887 of
                                        { Symbolic.One arg888 ->
                                            case lbl886 of
                                              { Label_S ->
                                                  Symbolic.peek arg888 Prelude.>>= \ d ->
                                                  Prelude.return con_False
                                              ; Label_Z -> Prelude.return con_True
                                              }
                                        })
                             }
                       }
                 })
      }
hbmc__lt__equal_ =
  \ ds ds896 ->
    case ds of
      { D_Nat tmp935 ->
          Symbolic.switch
            tmp935
            (\ lbl932 args933 ->
               case args933 of
                 { Symbolic.One arg934 ->
                     case lbl932 of
                       { Label_S ->
                           Symbolic.peek arg934 Prelude.>>= \ d ->
                           (case ds896 of
                              { D_Nat tmp931 ->
                                  Symbolic.switch
                                    tmp931
                                    (\ lbl928 args929 ->
                                       case args929 of
                                         { Symbolic.One arg930 ->
                                             case lbl928 of
                                               { Label_S ->
                                                   Symbolic.peek arg930 Prelude.>>= \ d897 ->
                                                   Prelude.return (Symbolic.The ((,) d d897))
                                                     Prelude.>>= \ arg894 ->
                                                   Symbolic.peek arg894 Prelude.>>= \ tmp925 ->
                                                   Symbolic.peek arg894 Prelude.>>= \ tmp926 ->
                                                   hbmc__lt__equal_
                                                     (Prelude.fst tmp925) (Prelude.snd tmp926)
                                                     Prelude.>>= \ tmp927 ->
                                                   Symbolic.peek (Symbolic.The tmp927)
                                               ; Label_Z -> Prelude.return con_False
                                               }
                                         })
                              })
                       ; Label_Z -> Prelude.return con_True
                       }
                 })
      }
hbmc__plus__plus_ =
  \ ds ys ->
    case ds of
      { D__rbrack__lbrack_ tmp976 ->
          Symbolic.switch
            tmp976
            (\ lbl972 args973 ->
               case args973 of
                 { (,) arg974 arg975 ->
                     case lbl972 of
                       { Label__rbrack__lbrack_ -> Prelude.return ys
                       ; Label__cons_ ->
                           Symbolic.peek arg975 Prelude.>>= \ xs ->
                           Symbolic.peek arg974 Prelude.>>= \ x ->
                           Prelude.return (Symbolic.The ((,) xs ys)) Prelude.>>= \ arg936 ->
                           Symbolic.peek arg936 Prelude.>>= \ tmp969 ->
                           Symbolic.peek arg936 Prelude.>>= \ tmp970 ->
                           hbmc__plus__plus_ (Prelude.fst tmp969) (Prelude.snd tmp970)
                             Prelude.>>= \ tmp971 ->
                           Symbolic.peek (Symbolic.The tmp971) Prelude.>>= \ tmp968 ->
                           Prelude.return (con__cons_ x tmp968)
                       }
                 })
      }
hbmc__plus_ =
  \ ds y ->
    case ds of
      { D_Nat tmp1013 ->
          Symbolic.switch
            tmp1013
            (\ lbl1010 args1011 ->
               case args1011 of
                 { Symbolic.One arg1012 ->
                     case lbl1010 of
                       { Label_S ->
                           Symbolic.peek arg1012 Prelude.>>= \ x ->
                           Prelude.return (Symbolic.The ((,) x y)) Prelude.>>= \ arg977 ->
                           Symbolic.peek arg977 Prelude.>>= \ tmp1007 ->
                           Symbolic.peek arg977 Prelude.>>= \ tmp1008 ->
                           hbmc__plus_ (Prelude.fst tmp1007) (Prelude.snd tmp1008)
                             Prelude.>>= \ tmp1009 ->
                           Symbolic.peek (Symbolic.The tmp1009) Prelude.>>= \ tmp1006 ->
                           Prelude.return (con_S tmp1006)
                       ; Label_Z -> Prelude.return y
                       }
                 })
      }
hbmc__mul_ =
  \ ds ds1016 ->
    case ds of
      { D_Nat tmp1052 ->
          Symbolic.switch
            tmp1052
            (\ lbl1049 args1050 ->
               case args1050 of
                 { Symbolic.One arg1051 ->
                     case lbl1049 of
                       { Label_S ->
                           Symbolic.peek arg1051 Prelude.>>= \ x ->
                           Prelude.return (Symbolic.The ((,) x ds1016))
                             Prelude.>>= \ arg1014 ->
                           Symbolic.peek arg1014 Prelude.>>= \ tmp1046 ->
                           Symbolic.peek arg1014 Prelude.>>= \ tmp1047 ->
                           hbmc__mul_ (Prelude.fst tmp1046) (Prelude.snd tmp1047)
                             Prelude.>>= \ tmp1048 ->
                           (Symbolic.peek (Symbolic.The tmp1048)) Prelude.>>=
                           (hbmc__plus_ ds1016)
                       ; Label_Z -> Prelude.return con_Z
                       }
                 })
      }
hbmc__and__and_ =
  \ ds x ->
    case ds of
      { D_Bool tmp1056 ->
          Symbolic.switch
            tmp1056
            (\ lbl1054 args1055 ->
               case args1055 of
                 { () ->
                     case lbl1054 of
                       { Label_False -> Prelude.return con_False
                       ; Label_True -> Prelude.return x
                       }
                 })
      }
hbmc_prop_app_inj1 =
  (Symbolic.io (Prelude.putStrLn "Generating symbolic values..."))
    Prelude.>>
  (new__rbrack__lbrack_ gbl_size (Symbolic.newNat gbl_size)
     Prelude.>>= \ zs ->
   new__rbrack__lbrack_ gbl_size (Symbolic.newNat gbl_size)
     Prelude.>>= \ ys ->
   new__rbrack__lbrack_ gbl_size (Symbolic.newNat gbl_size)
     Prelude.>>= \ xs ->
   (Symbolic.io (Prelude.putStrLn "Running functions...")) Prelude.>>
   (hbmc__plus__plus_ xs ys Prelude.>>= \ tmp1069 ->
    hbmc__plus__plus_ xs zs Prelude.>>= \ tmp1070 ->
    Symbolic.equal tmp1069 tmp1070 Prelude.>>= \ l1068 ->
    (Symbolic.addClause (l1068 : ([]))) Prelude.>>
    (Symbolic.equal ys zs Prelude.>>= \ l1059 ->
     (Symbolic.addClause ((Symbolic.nt l1059) : ([]))) Prelude.>>
     ((Symbolic.io (Prelude.putStrLn "Running solver...")) Prelude.>>
      (Symbolic.check Prelude.>>
       ((Symbolic.io (Prelude.putStrLn "Done!")) Prelude.>>
        (Symbolic.get ((,,) xs ys zs))))))))
hbmc_prop_app_inj2 =
  (Symbolic.io (Prelude.putStrLn "Generating symbolic values..."))
    Prelude.>>
  (new__rbrack__lbrack_ gbl_size (Symbolic.newNat gbl_size)
     Prelude.>>= \ zs ->
   new__rbrack__lbrack_ gbl_size (Symbolic.newNat gbl_size)
     Prelude.>>= \ ys ->
   new__rbrack__lbrack_ gbl_size (Symbolic.newNat gbl_size)
     Prelude.>>= \ xs ->
   (Symbolic.io (Prelude.putStrLn "Running functions...")) Prelude.>>
   (hbmc__plus__plus_ xs ys Prelude.>>= \ tmp1083 ->
    hbmc__plus__plus_ zs ys Prelude.>>= \ tmp1084 ->
    Symbolic.equal tmp1083 tmp1084 Prelude.>>= \ l1082 ->
    (Symbolic.addClause (l1082 : ([]))) Prelude.>>
    (Symbolic.equal xs zs Prelude.>>= \ l1073 ->
     (Symbolic.addClause ((Symbolic.nt l1073) : ([]))) Prelude.>>
     ((Symbolic.io (Prelude.putStrLn "Running solver...")) Prelude.>>
      (Symbolic.check Prelude.>>
       ((Symbolic.io (Prelude.putStrLn "Done!")) Prelude.>>
        (Symbolic.get ((,,) xs ys zs))))))))
hbmc_prop_len_bs =
  (Symbolic.io (Prelude.putStrLn "Generating symbolic values..."))
    Prelude.>>
  (new__rbrack__lbrack_ gbl_size (Symbolic.newNat gbl_size)
     Prelude.>>= \ ys ->
   new__rbrack__lbrack_ gbl_size (Symbolic.newNat gbl_size)
     Prelude.>>= \ xs ->
   (Symbolic.io (Prelude.putStrLn "Running functions...")) Prelude.>>
   (hbmc__plus__plus_ xs ys Prelude.>>= \ tmp1096 ->
    hbmc_length tmp1096 Prelude.>>= \ tmp1097 ->
    hbmc_length xs Prelude.>>= \ tmp1098 ->
    Symbolic.equal tmp1097 tmp1098 Prelude.>>= \ l1095 ->
    (Symbolic.addClause ((Symbolic.nt l1095) : ([]))) Prelude.>>
    ((Symbolic.io (Prelude.putStrLn "Running solver...")) Prelude.>>
     (Symbolic.check Prelude.>>
      ((Symbolic.io (Prelude.putStrLn "Done!")) Prelude.>>
       (Symbolic.get ((,) xs ys)))))))
gbl_size = 5 :: Prelude.Int
--main = do {Prelude.putStrLn "\n====== hbmc_prop_app_inj1 ======"; Prelude.print Prelude.=<< Symbolic.runH hbmc_prop_app_inj1; Prelude.putStrLn "\n====== hbmc_prop_app_inj2 ======"; Prelude.print Prelude.=<< Symbolic.runH hbmc_prop_app_inj2; Prelude.putStrLn "\n====== hbmc_prop_len_bs ======"; Prelude.print Prelude.=<< Symbolic.runH hbmc_prop_len_bs}

main = do
    (The (vars,lits),s) <- escapeH $ do
        abs <- ["x","y","z"] `makeVars` Symbolic.newNat gbl_size
        nats <- ["m","n","o"] {- "A","B"] -} `makeVars` new_Nat gbl_size
        lists <- ["xs","ys","zs","vs","ws" {- ,"ps","qs" -}] `makeVars` new__rbrack__lbrack_ gbl_size (Symbolic.newNat gbl_size)
        lits <- sequence $
            {-
            [ do b <- equal rs =<< hbmc_drop n xs
                 return (Def "drop" [name_n,name_xs] name_rs,nt b)
            | (name_n, n) <- nats
            , (name_xs,xs) <- lists
            , (name_rs,rs) <- lists
            ] ++
            -}
            [ do b <- equal rs =<< hbmc__plus__plus_ xs ys
                 return (Def "++" [name_xs,name_ys] name_rs,nt b)
            | (name_xs,xs) <- lists
            , (name_ys,ys) <- lists
            , (name_rs,rs) <- lists
            ] ++
            [ do b <- equal r =<< hbmc_length xs
                 return (Def "length" [name_xs] name_r,nt b)
            | (name_xs,xs) <- lists
            , (name_r, r) <- nats
            ] ++
            [ do b <- equal rs =<< hbmc_rotate n xs
                 return (Def "rotate" [name_n,name_xs] name_rs,nt b)
            | (name_n, n) <- nats
            , (name_xs,xs) <- lists
            , (name_rs,rs) <- lists
            ] ++
            [ do b <- equal rs con__rbrack__lbrack_
                 return (Def "[]" [] name_rs,nt b)
            | (name_rs,rs) <- lists
            ] ++
            [ do b <- equal rs (con__cons_ x xs)
                 return (Def ":" [name_x,name_xs] name_rs,nt b)
            | (name_x,x)   <- abs
            , (name_xs,xs) <- lists
            , (name_rs,rs) <- lists
            ] ++
            [ do b <- equal x y
                 return (Eq name_x name_y,b)
            | (name_x,x):_ <- [nats]
            , _:(name_y,y):_ <- [nats]
            , name_x Prelude.< name_y
            ] ++
            [ do b <- equal xs ys
                 return (Eq name_xs name_ys,b)
            | (name_xs,xs):_ <- [lists]
            , _:(name_ys,ys):_ <- [lists]
            , name_xs Prelude.< name_ys
            ]
        return ([Prelude.map Prelude.fst nats,Prelude.map Prelude.fst lists,Prelude.map Prelude.fst abs],lits)
    turboString vars lits s

