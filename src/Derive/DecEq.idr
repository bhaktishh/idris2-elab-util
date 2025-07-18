module Derive.DecEq

import Language.Reflection.Util 
import Decidable.Equality
import Language.Reflection.Pretty
import Language.Reflection.Syntax.Ops
import Data.Vect

%default total

%language ElabReflection

ttImpCouldBeSame : (TTImp, TTImp) -> Bool
ttImpCouldBeSame (IVar _ n1, IVar _ n2) = ?ithinkineedelab
ttImpCouldBeSame _ = ?idk

appArgSame : {a : _} -> {b : _} -> (AppArg a, AppArg b) -> Bool 
appArgSame (Regular t1, Regular t2) = ttImpCouldBeSame (t1, t2)
appArgSame (NamedApp _ t1, NamedApp _ t2) = ttImpCouldBeSame (t1, t2)
appArgSame (AutoApp t1, AutoApp t2) = ttImpCouldBeSame (t1, t2)
appArgSame _ = False 

allAppArgSame : {vs : Vect n Arg} -> AppArgs vs -> AppArgs vs -> Bool 
allAppArgSame {vs=[]} _ _ = True
allAppArgSame {vs=x::xs} (a :: as) (b :: bs) = appArgSame (a, b) && allAppArgSame {vs=xs} as bs 

conTySame : {vs : Vect n Arg} -> Con n vs -> Con n vs -> Bool 
conTySame {vs} (MkCon _ _ _ a) (MkCon _ _ _ b) = allAppArgSame a b

generateCases : {vs : Vect n Arg} -> List (Con n vs) -> Maybe (List (Con n vs, Con n vs))
generateCases [] = Just []
generateCases [x] = Just [(x,x)]
generateCases (x :: y :: xs) = 
  let xfst  = ((x, x) :: map (x,) (filter (\x' => conTySame x x') (y :: xs))) in
  let xfst'  = if conTySame y x then xfst ++ [(y, x)] else xfst in 
  (xfst ++) <$> if null xs then Just [(y, y)] else generateCases (y :: xs)

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

-- getConstraints :: List IAnnParam -> List ITm
-- getConstraints [] = []
-- getConstraints (IAnnParam (v, ITyTy) _ : xs) = ITmCon "DecEq" [ITmVar v] : getConstraints xs
-- getConstraints (IAnnParam (v, ITyFunc args) _ : xs) = getFuncConstraint v args [] [] : getConstraints xs
-- getConstraints (_ : xs) = getConstraints xs

-- getFuncConstraint :: String -> List (Maybe String, ITy) -> List (Maybe String, ITy) -> List String -> ITm
-- getFuncConstraint fv args acc facc = case unsnoc args of
--   Just (xs, x@(Just v, _)) -> getFuncConstraint fv xs (x : acc) (v : facc)
--   Just (xs, (Nothing, _)) -> getFuncConstraint fv xs acc facc
--   Nothing -> ITmTy (ITyFunc (acc ++ [(Nothing, ITyTm $ ITmCon "DecEq" [ITmFuncCall (ITmVar fv) (map ITmVar facc)])]))
getFuncConstraint : Maybe Name -> TTImp -> TTImp -> List (Maybe Name, TTImp) -> List Name -> Arg 
getFuncConstraint = ?wejfdk

getConstraints : List Arg -> List Arg 
getConstraints [] = []
getConstraints (MkArg _ _ n (IType _) :: xs) = MkArg MW AutoImplicit Nothing (var "DecEq" .$ var (fromMaybe (UN Underscore) n)) :: getConstraints xs 
getConstraints (MkArg _ _ n (IPi _ _ _ mn argTy retTy) :: xs) = getFuncConstraint mn argTy retTy [] [] :: getConstraints xs
getConstraints (_ :: xs) = getConstraints xs 

export %inline
deriveDecEq : Elaboration m => TypeInfo -> m ()
deriveDecEq ti = 
	let Just cases = generateCases ti.cons 
	  | Nothing => fail "oupsi" in
	let 
		splitCons : {vs : Vect n Arg} -> Con n vs -> List (Maybe Name, Bool)
		splitCons {vs = vs} c = toList $ map (\(MkArg _ _ n ty) => (n, not (ty == type) && not (inConTy n c))) (snd $ Data.Vect.filter (\(MkArg _ i _ _) => i == ExplicitArg) c.args)

		mkConTm : {vs : Vect n Arg} -> String -> Con n vs -> TTImp 
		mkConTm i c = foldl (.$) (var c.name) (map (\(n, b) => if b then (var $ appToName i n) else (var $ fromMaybe (UN Underscore) n)) (splitCons c))

		implicits = map (\(MkArg x _ n ty) => MkArg x ImplicitArg n ty) ti.args

		mkClaim : ITy -> Decl 
		mkClaim ty = IClaim (MkFCVal EmptyFC (MkIClaimData { 
			rig = MW, 
			vis = Export, 
			opts = [Inline],
			type = ty
		}))

		mkClaimTy : TTImp -> List Arg -> TTImp 
		mkClaimTy = foldr (.->) 

		
	in 
		?wjek


-- case generateCases iTyDeclConstructors of
--       Nothing -> error "this type probably does not have decidable equality, soz"
--       Just cases ->
--         let hasTyTy c = map (\(IAnnParam (v, ty) _) -> (v, ty `notElem` dontDoTheseTypes && not (inConTy v (iConTy c)))) $ filter (\(IAnnParam (_, _) b) -> b) (iConArgs c)
--             tms i c = ITmCon (iConName c) (map (\(v, b) -> if b then ITmVar (v ++ i) else ITmVar v) (hasTyTy c))
--             implicits = map (\(IAnnParam (v, ty) _) -> IAnnParam (v, ty) False) iTyDeclParams
--          in Impl
--               { iImplicits = implicits,
--                 iConstraints = getConstraints iTyDeclParams,
--                 iSubject = ITmCon iTyDeclName (map (ITmVar . getIAnnParamVar) iTyDeclParams),
--                 iBody = concatMap (getCases . \(x, y) -> (tms "1" x, tms "2" y)) cases
--               }



-- -- this is the toplevel generation function. `derive` itself will do the declarations, you just return the toplevel stuff here. 

-- export %inline
-- DecEq : List Name -> ParamTypeInfo -> Res (List TopLevel)
-- DecEq xs (MkParamTypeInfo (MkTypeInfo {name, arty, args, argNames, cons}) pat pnames pcons pargs) = ?huh


-- tySame : (String, Vect n Arg) -> (String, Vect n Arg) -> Bool 
-- tySame (c1, args1) (c2, args2) = c1 == c2 && all argSame (zip args1 args2)

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