module Derive.DecEq

import Language.Reflection.Util 
import Decidable.Equality
import Language.Reflection.Pretty
import Language.Reflection.Syntax.Ops
import Data.Vect

%default total

%language ElabReflection

ttImpCouldBeSame : Elaboration m => (TTImp, TTImp) -> m Bool
ttImpCouldBeSame (IVar _ n1, IVar _ n2) = ?ejksdfgv
ttImpCouldBeSame _ = ?idk

appArgSame : Elaboration m => {a : _} -> {b : _} -> (AppArg a, AppArg b) -> m Bool 
appArgSame (Regular t1, Regular t2) = ttImpCouldBeSame (t1, t2)
appArgSame (NamedApp _ t1, NamedApp _ t2) = ttImpCouldBeSame (t1, t2)
appArgSame (AutoApp t1, AutoApp t2) = ttImpCouldBeSame (t1, t2)
appArgSame _ = pure False 

allAppArgSame : Elaboration m => {vs : Vect n Arg} -> AppArgs vs -> AppArgs vs -> m Bool 
allAppArgSame {vs=[]} _ _ = pure True
allAppArgSame {vs=x::xs} (a :: as) (b :: bs) = do
	here <- appArgSame (a, b)
	there <- allAppArgSame {vs=xs} as bs
	pure $ here && there

conTySame : Elaboration m => {vs : Vect n Arg} -> Con n vs -> Con n vs -> m Bool 
conTySame {vs} (MkCon _ _ _ a) (MkCon _ _ _ b) = allAppArgSame a b

doFilter : Elaboration m => {vs : Vect n Arg} -> (Con n vs) -> List (Con n vs) -> m (List (Con n vs))
doFilter x [] = pure []
doFilter {vs=vs} x (c::cs) = do 
	x' <- conTySame x c
	rest <- doFilter x cs
	if x' then pure (c :: rest) else pure rest  

generateCases : Elaboration m => {vs : Vect n Arg} -> List (Con n vs) -> m (Maybe (List (Con n vs, Con n vs)))
generateCases [] = pure $ Just []
generateCases [x] = pure $ Just [(x,x)]
generateCases {vs=vs} (x :: y :: xs) = do 
  filtered <- doFilter {vs=vs} x (y :: xs)
  let xfst  = ((x, x) :: map (x,) filtered)
  b <- conTySame y x 
  let xfst'  = if b then xfst ++ [(y, x)] else xfst
  (xfst ++) <$> if null xs then pure (Just (Prelude.Basics.(::) (y, y) [])) else generateCases (y :: xs)

appToName : String -> Maybe Name -> Name 
appToName s (Just $ NS ns n) = NS ns (appToName s (Just n))
appToName s (Just $ UN (Basic str)) = UN (Basic (str ++ s))
appToName s (Just $ UN (Field str)) = UN (Field (str ++ s))
appToName s (Just $ UN Underscore) = UN Underscore --todo 
appToName s (Just $ MN str i) = MN (str ++ s) i
appToName s (Just $ DN str i) = DN (str ++ s) i
appToName s (Just $ Nested i nm) = Nested i (appToName s (Just nm))
appToName s (Just $ CaseBlock str i) = CaseBlock (str ++ s) i
appToName s (Just $ WithBlock str i) = WithBlock (str ++ s) i 
appToName _ Nothing = UN Underscore 

inConTy : {vs : Vect n Arg} -> Maybe Name -> Con n vs -> Bool 
inConTy {vs=vs} (Just n) _ = any (\a => ttImpCouldBeSame (var n, a.type)) vs
inConTy Nothing _ = False 

getFuncConstraint : Maybe Name -> Name -> TTImp -> TTImp -> List (Maybe Name, TTImp) -> List Name -> Arg
getFuncConstraint n mn argTy (IPi _ _ _ n' arg' ret') acc facc = getFuncConstraint n mn argTy ret' ((n', arg') :: acc) (fromMaybe (UN Underscore) n' :: facc)
getFuncConstraint n mn argTy _ acc facc = 
	let fst : TTImp = IApp EmptyFC (var "DecEq") (foldl (IApp EmptyFC) (var (fromMaybe (UN Underscore) n)) (map var facc)) in 
		MkArg MW ExplicitArg n (foldr (.->) fst (map (\(n, t) => MkArg MW ExplicitArg n t) acc))

getConstraints : List Arg -> List Arg 
getConstraints [] = []
getConstraints (MkArg _ _ n (IType _) :: xs) = MkArg MW AutoImplicit Nothing (var "DecEq" .$ var (fromMaybe (UN Underscore) n)) :: getConstraints xs 
getConstraints (MkArg _ _ n (IPi _ _ _ mn argTy retTy) :: xs) = getFuncConstraint n (fromMaybe (UN Underscore) mn) argTy retTy [] [] :: getConstraints xs
getConstraints (_ :: xs) = getConstraints xs 

deriveDecEqDef : Elaboration m => TypeInfo -> m Decl 
deriveDecEqDef ti =
	let Just cases = generateCases ti.cons 
	  | Nothing => ?ejkdfg in
	let 
		splitCons : {vs : Vect n Arg} -> Con n vs -> List (Maybe Name, Bool)
		splitCons {vs = vs} c = toList $ map (\(MkArg _ _ n ty) => (n, not (ty == type) && not (inConTy n c))) (snd $ Data.Vect.filter (\(MkArg _ i _ _) => i == ExplicitArg) c.args)

		mkConTm : {vs : Vect n Arg} -> String -> Con n vs -> TTImp 
		mkConTm i c = foldl (.$) (var c.name) (map (\(n, b) => if b then (var $ appToName i n) else (var $ fromMaybe (UN Underscore) n)) (splitCons c))
	in 
		?ejrkdfg

deriveDecEqClaim : TypeInfo -> Decl 
deriveDecEqClaim ti =
	let 
		implicits = toList $ map (\(MkArg x _ n ty) => MkArg x ImplicitArg n ty) ti.args
		constraints = getConstraints (toList ti.args)
		final = var "DecEq" .$ ((foldl (.$) (var ti.name) (map var ti.argNames)))
		prev = implicits ++ constraints 

		claimTy = foldr (.->) final prev 
	in
		interfaceHint Public "decEq" claimTy

export %inline
deriveDecEq : Elaboration m => TypeInfo -> m ()
deriveDecEq ti = declare [deriveDecEqClaim ti]

decEqInfo : TypeInfo 
decEqInfo = MkTypeInfo
  { name = "Decidable.Equality.Core.DecEq"
  , arty = 1
  , args = [MkArg MW ExplicitArg (Just "t") (hole "_")]
  , argNames = ["t"]
  , cons =
      [ MkCon
          { name =
              "Decidable.Equality.Core.DecEq at Decidable.Equality.Core:11:1--15:48"
          , arty = 2
          , args =
              [ MkArg M0 ImplicitArg (Just "t") type
              , MkArg
                  MW
                  ExplicitArg
                  (Just "decEq")
                  (    MkArg MW ExplicitArg (Just "x1") (var "t")
                   .-> MkArg MW ExplicitArg (Just "x2") (var "t")
                   .->    var "Prelude.Types.Dec"
                       .$ (   var "Builtin.(===)"
                           .! ("a", var "t")
                           .$ var "x1"
                           .$ var "x2"))
              ]
          , typeArgs = [Regular (var "t")]
          }
      ]
  }

data Vect' : (n : Nat) -> (t : Type) -> Type where 
	Nil' : Vect' 0 t
	Cons' : (head : t) -> (tail : Vect' n t) -> Vect' (S n) t

{n : Nat} -> {t : Type} -> (DecEq t) => DecEq (Vect' n t) where 
	decEq (Nil') (Nil') = Yes Refl
	decEq (Cons' head1 tail1) (Cons' head2 tail2) with (decEq head1 head2)
		decEq (Cons' head1 tail1) (Cons' head1 tail2) | Yes Refl  with (decEq tail1 tail2)
			decEq (Cons' head1 tail1) (Cons' head1 tail1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (Cons' head1 tail1) (Cons' head1 tail2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (Cons' head1 tail1) (Cons' head2 tail2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))


data D1 : (t : Type) -> Type where
	C1 : (x : t) -> D1 t

D1Info : TypeInfo 
D1Info = MkTypeInfo
  { name = "Derive.DecEq.D1"
  , arty = 1
  , args = [MkArg MW ExplicitArg (Just "t") type]
  , argNames = ["t"]
  , cons =
      [ MkCon
          { name = "Derive.DecEq.C1"
          , arty = 2
          , args =
              [ MkArg M0 ImplicitArg (Just "t") type
              , MkArg MW ExplicitArg (Just "x") (var "t")
              ]
          , typeArgs = [Regular (var "t")]
          }
      ]
  }

%runElab deriveDecEq D1Info

x = `[ 
	export %inline 
	decEq : {t : Type} -> DecEq t => (a : D1 t) -> (b : D1 t) -> Dec (a = b)
	decEq (C1 x) (C1 y) with (decEq x y)
		decEq (C1 x) (C1 x) | Yes Refl = Yes Refl 
		decEq (C1 x) (C1 y) | No prf = No (\h => prf $ case h of Refl => Refl)
]


-- TODO pretty printer broken for IClaim
y : List Decl
y = [ IClaim
    (MkFCVal EmptyFC (MkIClaimData
       { rig = MW
       , vis = Export
       , opts = [Inline]
       , type =
           mkTy
             { name = "decEq"
             , type =
                     MkArg MW ImplicitArg (Just "t") type
                 .-> MkArg MW AutoImplicit Nothing (var "DecEq" .$ var "t")
                 .-> MkArg MW ExplicitArg (Just "a") (var "D1" .$ var "t")
                 .-> MkArg MW ExplicitArg (Just "b") (var "D1" .$ var "t")
                 .->    var "Dec"
                     .$ alternative
                          { tpe = FirstSuccess
                          , alts =
                              [ var "===" .$ var "a" .$ var "b"
                              , var "~=~" .$ var "a" .$ var "b"
                              ]
                          }
             }
       }))
, IDef
    emptyFC
    "decEq"
    [ withClause
        { lhs =
               var "decEq"
            .$ (var "C1" .$ bindVar "x")
            .$ (var "C1" .$ bindVar "y")
        , rig = MW
        , wval = var "decEq" .$ var "x" .$ var "y"
        , prf = Nothing
        , flags = []
        , clauses =
            [    withApp
                   { fun =
                          var "decEq"
                       .$ (var "C1" .$ bindVar "x")
                       .$ (var "C1" .$ bindVar "x")
                   , arg = var "Yes" .$ var "Refl"
                   }
              .= var "Yes" .$ var "Refl"
            ,    withApp
                   { fun =
                          var "decEq"
                       .$ (var "C1" .$ bindVar "x")
                       .$ (var "C1" .$ bindVar "y")
                   , arg = var "No" .$ bindVar "prf"
                   }
              .=    var "No"
                 .$ (    MkArg MW ExplicitArg (Just "h") implicitFalse
                     .=>    var "prf"
                         .$ iCase
                              { sc = var "h"
                              , ty = implicitFalse
                              , clauses = [var "Refl" .= var "Refl"]
                              })
            ]
        }
    ]
]

vectInfo = MkTypeInfo
  { name = "Data.Vect.Vect"
  , arty = 2
  , args =
      [ MkArg MW ExplicitArg (Just "len") (var "Prelude.Types.Nat")
      , MkArg MW ExplicitArg (Just "elem") type
      ]
  , argNames = ["len", "elem"]
  , cons =
      [ MkCon
          { name = "Data.Vect.Nil"
          , arty = 1
          , args = [MkArg M0 ImplicitArg (Just "elem") type]
          , typeArgs = [Regular (var "Prelude.Types.Z"), Regular (var "elem")]
          }
      , MkCon
          { name = "Data.Vect.(::)"
          , arty = 4
          , args =
              [ MkArg M0 ImplicitArg (Just "len") (var "Prelude.Types.Nat")
              , MkArg M0 ImplicitArg (Just "elem") type
              , MkArg MW ExplicitArg (Just "x") (var "elem")
              , MkArg
                  MW
                  ExplicitArg
                  (Just "xs")
                  (var "Data.Vect.Vect" .$ var "len" .$ var "elem")
              ]
          , typeArgs =
              [ Regular (var "Prelude.Types.S" .$ var "len")
              , Regular (var "elem")
              ]
          }
      ]
  }

data MyCurse : (a : Type) -> (b : (x : a) -> Type) -> (p : (x : a) -> (y : (b x)) -> Type) -> Type where 
	MkMyCurse : {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> (x : a) -> (y : (b x)) -> (pf : (p x y)) -> MyCurse a b p

myCurseInfo = MkTypeInfo
  { name = "Derive.DecEq.MyCurse"
  , arty = 3
  , args =
      [ MkArg MW ExplicitArg (Just "a") type
      , MkArg
          MW
          ExplicitArg
          (Just "b")
          (MkArg MW ExplicitArg (Just "x") (var "a") .-> type)
      , MkArg
          MW
          ExplicitArg
          (Just "p")
          (    MkArg MW ExplicitArg (Just "x") (var "a")
           .-> MkArg MW ExplicitArg (Just "y") (var "b" .$ var "x")
           .-> type)
      ]
  , argNames = ["a", "b", "p"]
  , cons =
      [ MkCon
          { name = "Derive.DecEq.MkMyCurse"
          , arty = 6
          , args =
              [ MkArg MW ImplicitArg (Just "a") type
              , MkArg
                  MW
                  ImplicitArg
                  (Just "b")
                  (MkArg MW ExplicitArg (Just "x") (var "a") .-> type)
              , MkArg
                  MW
                  ImplicitArg
                  (Just "p")
                  (    MkArg MW ExplicitArg (Just "x") (var "a")
                   .-> MkArg MW ExplicitArg (Just "y") (var "b" .$ var "x")
                   .-> type)
              , MkArg MW ExplicitArg (Just "x") (var "a")
              , MkArg MW ExplicitArg (Just "y") (var "b" .$ var "x")
              , MkArg MW ExplicitArg (Just "pf") (var "p" .$ var "x" .$ var "y")
              ]
          , typeArgs = [Regular (var "a"), Regular (var "b"), Regular (var "p")]
          }
      ]
  }

myCurseDer = `[
	export %inline 
	decEq : {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> ((DecEq a)) => ((x : a) -> (DecEq (b x))) => ((x : a) -> (y : (b x)) -> (DecEq (p x y))) => DecEq ((MyCurse a b p)) 
	decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) with (decEq x1 x2)
		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | (Yes Refl)  with (decEq y1 y2)
			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | (Yes Refl) | (Yes Refl)  with (decEq pf1 pf2)
				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf1) | (Yes Refl) | (Yes Refl) | (Yes Refl)  = (Yes Refl)
				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | (Yes Refl) | (Yes Refl) | (No prf)  = (No (\h => (prf (case (h) of
					((Refl)) => (Refl)))))
			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | (Yes Refl) | (No prf)  = (No (\h => (prf (case (h) of
				((Refl)) => (Refl)))))
		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) | (No prf)  = (No (\h => (prf (case (h) of
			((Refl)) => (Refl)))))
]

myCurseDerInfo : List Decl 
myCurseDerInfo = [ IClaim
    (MkFCVal EmptyFC (MkIClaimData
       { rig = MW
       , vis = Export
       , opts = [Inline]
       , type =
           mkTy
             { name = "decEq"
             , type =
                     MkArg MW ImplicitArg (Just "a") type
                 .-> MkArg
                       MW
                       ImplicitArg
                       (Just "b")
                       (MkArg MW ExplicitArg (Just "x") (var "a") .-> type)
                 .-> MkArg
                       MW
                       ImplicitArg
                       (Just "p")
                       (    MkArg MW ExplicitArg (Just "x") (var "a")
                        .-> MkArg
                              MW
                              ExplicitArg
                              (Just "y")
                              (var "b" .$ var "x")
                        .-> type)
                 .-> MkArg MW AutoImplicit Nothing (var "DecEq" .$ var "a")
                 .-> MkArg
                       MW
                       AutoImplicit
                       Nothing
                       (    MkArg MW ExplicitArg (Just "x") (var "a")
                        .-> var "DecEq" .$ (var "b" .$ var "x"))
                 .-> MkArg
                       MW
                       AutoImplicit
                       Nothing
                       (MkArg MW ExplicitArg (Just "x") (var "a")
                        .-> MkArg
                              MW
                              ExplicitArg
                              (Just "y")
                              (var "b" .$ var "x")
                        .-> var "DecEq" .$ (var "p" .$ var "x" .$ var "y"))
                 .->    var "DecEq"
                     .$ (var "MyCurse" .$ var "a" .$ var "b" .$ var "p")
             }
       }))
, IDef
    emptyFC
    "decEq"
    [ withClause
        { lhs =
               var "decEq"
            .$ (   var "MkMyCurse"
                .$ bindVar "x1"
                .$ bindVar "y1"
                .$ bindVar "pf1")
            .$ (   var "MkMyCurse"
                .$ bindVar "x2"
                .$ bindVar "y2"
                .$ bindVar "pf2")
        , rig = MW
        , wval = var "decEq" .$ var "x1" .$ var "x2"
        , prf = Nothing
        , flags = []
        , clauses =
            [ withClause
                { lhs =
                    withApp
                      { fun =
                             var "decEq"
                          .$ (   var "MkMyCurse"
                              .$ bindVar "x1"
                              .$ bindVar "y1"
                              .$ bindVar "pf1")
                          .$ (   var "MkMyCurse"
                              .$ bindVar "x1"
                              .$ bindVar "y2"
                              .$ bindVar "pf2")
                      , arg = var "Yes" .$ var "Refl"
                      }
                , rig = MW
                , wval = var "decEq" .$ var "y1" .$ var "y2"
                , prf = Nothing
                , flags = []
                , clauses =
                    [ withClause
                        { lhs =
                            withApp
                              { fun =
                                  withApp
                                    { fun =
                                           var "decEq"
                                        .$ (   var "MkMyCurse"
                                            .$ bindVar "x1"
                                            .$ bindVar "y1"
                                            .$ bindVar "pf1")
                                        .$ (   var "MkMyCurse"
                                            .$ bindVar "x1"
                                            .$ bindVar "y1"
                                            .$ bindVar "pf2")
                                    , arg = var "Yes" .$ var "Refl"
                                    }
                              , arg = var "Yes" .$ var "Refl"
                              }
                        , rig = MW
                        , wval = var "decEq" .$ var "pf1" .$ var "pf2"
                        , prf = Nothing
                        , flags = []
                        , clauses =
                            [    withApp
                                   { fun =
                                       withApp
                                         { fun =
                                             withApp
                                               { fun =
                                                      var "decEq"
                                                   .$ (   var "MkMyCurse"
                                                       .$ bindVar "x1"
                                                       .$ bindVar "y1"
                                                       .$ bindVar "pf1")
                                                   .$ (   var "MkMyCurse"
                                                       .$ bindVar "x1"
                                                       .$ bindVar "y1"
                                                       .$ bindVar "pf1")
                                               , arg = var "Yes" .$ var "Refl"
                                               }
                                         , arg = var "Yes" .$ var "Refl"
                                         }
                                   , arg = var "Yes" .$ var "Refl"
                                   }
                              .= var "Yes" .$ var "Refl"
                            ,    withApp
                                   { fun =
                                       withApp
                                         { fun =
                                             withApp
                                               { fun =
                                                      var "decEq"
                                                   .$ (   var "MkMyCurse"
                                                       .$ bindVar "x1"
                                                       .$ bindVar "y1"
                                                       .$ bindVar "pf1")
                                                   .$ (   var "MkMyCurse"
                                                       .$ bindVar "x1"
                                                       .$ bindVar "y1"
                                                       .$ bindVar "pf2")
                                               , arg = var "Yes" .$ var "Refl"
                                               }
                                         , arg = var "Yes" .$ var "Refl"
                                         }
                                   , arg = var "No" .$ bindVar "prf"
                                   }
                              .=    var "No"
                                 .$ (    MkArg
                                           MW
                                           ExplicitArg
                                           (Just "h")
                                           implicitFalse
                                     .=>    var "prf"
                                         .$ iCase
                                              { sc = var "h"
                                              , ty = implicitFalse
                                              , clauses =
                                                  [var "Refl" .= var "Refl"]
                                              })
                            ]
                        }
                    ,    withApp
                           { fun =
                               withApp
                                 { fun =
                                        var "decEq"
                                     .$ (   var "MkMyCurse"
                                         .$ bindVar "x1"
                                         .$ bindVar "y1"
                                         .$ bindVar "pf1")
                                     .$ (   var "MkMyCurse"
                                         .$ bindVar "x1"
                                         .$ bindVar "y2"
                                         .$ bindVar "pf2")
                                 , arg = var "Yes" .$ var "Refl"
                                 }
                           , arg = var "No" .$ bindVar "prf"
                           }
                      .=    var "No"
                         .$ (    MkArg MW ExplicitArg (Just "h") implicitFalse
                             .=>    var "prf"
                                 .$ iCase
                                      { sc = var "h"
                                      , ty = implicitFalse
                                      , clauses = [var "Refl" .= var "Refl"]
                                      })
                    ]
                }
            ,    withApp
                   { fun =
                          var "decEq"
                       .$ (   var "MkMyCurse"
                           .$ bindVar "x1"
                           .$ bindVar "y1"
                           .$ bindVar "pf1")
                       .$ (   var "MkMyCurse"
                           .$ bindVar "x2"
                           .$ bindVar "y2"
                           .$ bindVar "pf2")
                   , arg = var "No" .$ bindVar "prf"
                   }
              .=    var "No"
                 .$ (    MkArg MW ExplicitArg (Just "h") implicitFalse
                     .=>    var "prf"
                         .$ iCase
                              { sc = var "h"
                              , ty = implicitFalse
                              , clauses = [var "Refl" .= var "Refl"]
                              })
            ]
        }
    ]
]