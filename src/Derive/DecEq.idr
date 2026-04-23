module Derive.DecEq

import Language.Reflection.Util 
import Decidable.Equality
import Language.Reflection.Pretty
import Language.Reflection.Syntax.Ops
import Language.Reflection
import Data.Vect
import Data.DPair
import Data.List1
import Data.List.Quantifiers

%default total
%language ElabReflection
%logging 1 

appToName : String -> Name -> Name 
appToName s (NS ns n) = NS ns (appToName s n)
appToName s (UN (Basic str)) = UN (Basic (str ++ s))
appToName s (UN (Field str)) = UN (Field (str ++ s))
appToName s (UN Underscore) = UN Underscore --todo 
appToName s (MN str i) = MN (str ++ s) i
appToName s (DN str i) = DN (str ++ s) i
appToName s (Nested i nm) = Nested i (appToName s nm)
appToName s (CaseBlock str i) = CaseBlock (str ++ s) i
appToName s (WithBlock str i) = WithBlock (str ++ s) i 

ttIncludes : Name -> TTImp -> Elab Bool 
ttIncludes n (IVar _ n') = pure $ n == n'
ttIncludes n (IApp _ t1 t2) = (||) <$> ttIncludes n t1 <*> (delay <$> ttIncludes n t2)
ttIncludes _ _ = pure False 

inConTy : Maybe Name -> (AppArgs vs) -> Elab Bool 
inConTy Nothing _ = pure False 
inConTy (Just n) Nil = pure False
inConTy (Just n) (Regular x :: xs) = (||) <$> ttIncludes n x <*> (delay <$> inConTy (Just n) xs)
inConTy _ _ = pure False 

deriveDecEqDef: TypeInfo -> List (String, String) -> Elab (List Clause) 
deriveDecEqDef ti casesStr = 
    let 
        -- for some constructor, the names of all explicit args and whether they are to be split on or not
        splitCons : {vs : Vect n Arg} -> Con n vs -> Elab (q ** Vect q (Name, Bool))
        splitCons {vs = vs} c = let 
            -- explicits only
            (p ** args) = filter (\(MkArg _ i _ _) => i == ExplicitArg) c.args 
            fr : Vect p Name = freshNames (nameStr c.name) p
            -- a list of args and fresh names for each arg
            v' : Vect p (Arg, Name) = zip {z=Vect p} args fr
            in do 
                xs : Vect p (Name, Bool) <- traverse (\((MkArg _ _ n ty), i) => do 
                    ict : Bool <- inConTy n c.typeArgs
                    pure $ (fromMaybe i n, not (ty == type) && not ict)) v'
                pure (p ** xs)
        
        -- makes a list of arguments for the constructor passed in. if the term needs to be split on, appends i to the variable for the term.
        mkArgs :  Maybe String -> Con ti.arty ti.args -> Elab (Name, (q ** Vect q Name))
        mkArgs i c = do 
            (p ** cons) <- splitCons c
            args : Vect p Name <- traverse (\(n, b) => pure $ if b then (appToName (fromMaybe "" i) n) else n) cons
            pure $ (c.name, (p ** args))
        
        -- make a ttimp from a constructor and its arguments 
        mkConTm : (Name, (q ** Vect q Name)) -> TTImp
        mkConTm (i, (_ ** cs)) = foldl (.$) (var i) (map bindVar cs) 
        
        -- constructor pairs from string pairs returned from elab call  
        strToCons : List (String, String) -> Elab (List (Con ti.arty ti.args, Con ti.arty ti.args))
        strToCons [] = pure []
        strToCons ((x, y) :: xs) = let 
            findf : String -> (Con n vs -> Bool)
            findf x = (\e => (nameStr (dropNS (fromString x)) == (nameStr (dropNS e.name))) || (e.name == fromString x)) in
                case (find (findf x) ti.cons, find (findf y) ti.cons) of 
                    (Just x', Just y') => (::) <$> pure (x', y') <*> (strToCons xs)
                    (_, _) => fail $ "error: names dont match :(\n" ++ x ++ "\n" ++ y ++ "\n" ++ concat (map (nameStr . (.name)) ti.cons)

        -- case for unequal constructors
        unEqCons : TTImp
        unEqCons = var "No" .$ (lam (MkArg MW ExplicitArg (Just "h") implicitFalse)
                   (iCase
                      { sc = var "h"
                        , ty = implicitFalse
                        , clauses = [ImpossibleClause EmptyFC (var "Refl")]
                      }))

        appNames : Name -> List Name -> TTImp
        appNames n xs = foldl (.$) (var n) (map bindVar xs)

        --  pass in the name of the constructor, the variables that have been resolved to equals for both terms, and the rest of the variables that need to be resolved
        --        conName dontSplit    withApp func              c1             c2
        mkWiths : Name -> List Name -> Maybe (TTImp -> TTImp) -> Vect p Name -> Vect p Name -> Elab Clause
        mkWiths cname cs Nothing Nil Nil = pure $ patClause {
            lhs = var "decEq" .$ appNames cname cs .$ appNames cname cs,
            rhs = var "Yes" .$ var "Refl"
        }
        mkWiths cname cs (Just wAppf) Nil Nil = pure $ patClause {
            lhs = wAppf (var "decEq" .$ appNames cname cs .$ appNames cname cs),
            rhs = var "Yes" .$ var "Refl"
        }
        mkWiths cname cs wArgf xv@(x :: xs) yv@(y :: ys) = case x == y of 
            -- if the first argument does not need to be split on, add it to the list of precursor arguments and proceed
            True => mkWiths cname (cs ++ [x]) wArgf xs ys
            -- if the first argument does need to be split on
            False => do
                -- make argument terms for pattern match
                let xtm = appNames cname (cs ++ toList xv)
                let ytm = appNames cname (cs ++ toList yv)
                -- make applied terms for yes and no cases
                let yesTm = var "decEq" .$ (appNames cname (cs ++ [x] ++ toList xs)) .$ (appNames cname (cs ++ [x] ++ toList ys))
                let noTm = var "decEq" .$ xtm .$ ytm 
                -- for the yes case, add first argument to precursors (as they are assumed to be equal), and update with wArg function to add one more layer
                yesClause <- mkWiths cname (cs ++ [x]) (Just (\x => withApp {
                    fun = (fromMaybe id wArgf) x, 
                    arg = var "Yes" .$ var "Refl"})) xs ys
                let noClause = patClause {
                    lhs = withApp {
                        fun = fromMaybe id wArgf $ noTm,
                        arg = var "No" .$ bindVar "prf"
                    },
                    rhs = var "No" .$ (lam (MkArg MW ExplicitArg (Just "h") implicitFalse) (var "prf" .$ iCase {
                        sc = var "h",
                        ty = implicitFalse, 
                        clauses = [var "Refl" .= var "Refl"]
                    }))
                }
                pure $ withClause {
                    lhs = fromMaybe id wArgf $ noTm, 
                    rig = MW, 
                    wval = var "Decidable.Equality.decEq" .$ var x .$ var y,
                    prf = Nothing, 
                    flags = [], 
                    clauses = [yesClause, noClause]
                }

        -- makes the clause for a specific pair of constructors 
        mkCase : (Con ti.arty ti.args, Con ti.arty ti.args) -> Elab Clause
        mkCase (c1, c2) = do
                c1'@(n1, (p ** args1)) <- mkArgs (Just "1") c1
                c2'@(n2, (q ** args2)) <- mkArgs (Just "2") c2
                case (n1 == n2) of 
                    False => pure $ patClause (var "decEq" .$ mkConTm c1' .$ mkConTm c2') unEqCons
                    True => case (decEq p q) of 
                        No _ => fail "same constructor, different # args (should not happen)"
                        Yes prf => mkWiths n1 [] Nothing (replace {p=(\x => Vect x Name)} prf args1) args2 
    in do 
        cases <- strToCons casesStr
        traverse mkCase cases

--                  funcName      arg     argTy    piRetTy  
getFuncConstraint : Maybe Name -> Name -> TTImp -> TTImp -> List (Maybe Name, TTImp) -> List Name -> Arg
getFuncConstraint n mn argTy (IPi _ _ _ n' arg' ret') acc facc = getFuncConstraint n mn argTy ret' ((n', arg') :: acc) (fromMaybe (UN Underscore) n' :: facc)
getFuncConstraint n mn argTy _ acc facc = 
	let fst : TTImp = IApp EmptyFC (var "DecEq") (foldl (IApp EmptyFC) (var (fromMaybe (UN Underscore) n)) (map var facc)) in 
		MkArg MW AutoImplicit Nothing (foldr (.->) fst (map (\(n, t) => MkArg MW ExplicitArg n t) acc))

getConstraints : List Arg -> List Arg 
getConstraints [] = []
getConstraints (MkArg _ _ n (IType _) :: xs) = MkArg MW AutoImplicit Nothing (var "DecEq" .$ var (fromMaybe (UN Underscore) n)) :: getConstraints xs 
getConstraints (MkArg _ _ n (IPi _ _ _ mn argTy retTy) :: xs) = getFuncConstraint n (fromMaybe (UN Underscore) mn) argTy retTy [(mn, argTy)] [(fromMaybe (UN Underscore) mn)] :: getConstraints xs
getConstraints (_ :: xs) = getConstraints xs 

--                             (claim for hint, claim for function)                 
deriveDecEqClaim : TypeInfo -> (TTImp, TTImp) 
deriveDecEqClaim ti = let 
    implicits = toList $ map (\(MkArg x _ n ty) => MkArg x ImplicitArg n ty) ti.args
    tyq = (foldl (.$) (var ti.name) (map var ti.argNames))
    explicits : List Arg = (MkArg MW ExplicitArg (Just (UN (Basic "t_x1"))) tyq) :: (MkArg MW ExplicitArg (Just (UN (Basic "t_x2"))) tyq) :: []
    constraints = getConstraints (toList ti.args)
    finalFunc = var "Dec" .$ (var "===" .$ bindVar "t_x1" .$ bindVar "t_x2")
    finalHint = var "DecEq" .$ tyq
    prev = implicits ++ constraints
    claimFuncTy = foldr (.->) finalFunc (prev ++ explicits)
    claimHintTy = foldr (.->) finalHint prev
    in
        (claimHintTy, claimFuncTy)

public export
deriveDecEq : a -> Elab ()
deriveDecEq a = do 
    IVar _ n <- quote a
        | _ => fail "not the right thing"
    ti <- Language.Reflection.Types.getInfo' n
    pairs : List (String, String) <- getCompPairs a
    defn <- deriveDecEqDef ti pairs
    let (clHint, clFunc) = deriveDecEqClaim ti
    let fName = UN . Basic $ "implDecEq" ++ (nameStr ti.name)
    let impl = local [private' (UN $ Basic "decEq") $ clFunc, 
                    def (UN $ Basic "decEq") defn] (var "__mkDecEq" .$ type (arg (varStr "decEq")))
    logMsg "auto" 1 $ "interfaceHint claim: " ++ show fName ++ " : " ++ show clHint
    logMsg "auto" 1 $ "interfaceHint def: " ++ show (def fName [var fName .= impl ])
    declare [interfaceHint Public fName clHint, def fName [var fName .= impl ]]

-- to use, %runElab deriveDecEq <Type>
-- example: %runElab deriveDecEq Vect
-- to check if it worked, :doc Vect should show a hint for DecEq

%runElab deriveDecEq Maybe

-- ------------------------------------------------------------------------
-- -- dsa-gen Parser/Value.idr

-- ||| The kind of values that can occur in a DSA
-- public export
-- data Value : Type where
--   -- "base cases"
--   ||| An Idris name
--   IdrName : (n : String) -> Value
--   ||| A literal number
--   LitVal  : (lit : Integer) -> Value

--   -- recursive structures
--   ||| A data constructor, potentially taking some arguments
--   DataVal : (dc : String) -> (args : Maybe $ List1 Value) -> Value
--   ||| An addition expression
--   AddExpr : (num : Value) -> (addend : Value) -> Value
--   ||| A tuple expression
--   Tuple : (fst : Value) -> (snd : Value) -> Value

-- ------------------------------------------------------------------------
-- -- dsa-gen Parser/Label.idr

-- ||| Taking an argument
-- |||   ":(val)"
-- public export
-- data TakeArg : Type where
--   Takes : (val : Value) -> TakeArg

-- ||| Depending on a value
-- |||   "?(val)"
-- public export
-- data DepArg : Type where
--   DepsOn : (val : Value) -> DepArg

-- ||| Producing a value
-- |||   "!(val)"
-- public export
-- data ProdArg : Type where
--   Produce : (val : Value) -> ProdArg

-- ||| A DSALabel either contains a plain command (which is a data constructor), or
-- ||| a command which contains up to 3 actions.
-- public export
-- data DSALabel : Type where
--   ||| A command without any arguments
--   PlainCmd : (cmd : String) -> DSALabel
--   ||| A command taking an argument
--   TakeCmd : (cmd : String) -> (arg : TakeArg) -> DSALabel
--   ||| A command depending on a value
--   DepCmd : (cmd : String) -> (dep : DepArg) -> DSALabel
--   ||| A command producing a value
--   ProdCmd : (cmd : String) -> (res : ProdArg) -> DSALabel
--   ||| A command taking an argument and depending on a value
--   TDCmd : (cmd : String) -> (arg : TakeArg) -> (dep : DepArg) -> DSALabel
--   ||| A command taking an argument and producing a value
--   TPCmd : (cmd : String) -> (arg : TakeArg) -> (res : ProdArg) -> DSALabel
--   ||| A command depending on a value and producing a value
--   DPCmd : (cmd : String) -> (dep : DepArg) -> (res : ProdArg) -> DSALabel
--   ||| A command taking an argument, depending on a value, and producing a value
--   TDPCmd :  (cmd : String)
--          -> (arg : TakeArg)
--          -> (dep : DepArg)
--          -> (res : ProdArg)
--          -> DSALabel


-- ------------------------------------------------------------------------
-- -- dsa-gen DSLv2.idr

-- ||| A proof that the `Value` is a data constructor value.
-- public export
-- data IsDataVal : Value -> Type where
--   ItIsDataVal : IsDataVal (DataVal _ _)

-- ||| A proof that the `DSALabel` is a plain command (i.e. takes no arguments).
-- public export
-- data IsPlainCmd : DSALabel -> Type where
--   ItIsPlain : IsPlainCmd (PlainCmd _)

-- -- we need the following `Uninhabited` instances for returning provably
-- -- non-plain commands

-- Uninhabited (IsPlainCmd (TakeCmd _ _)) where
--   uninhabited ItIsPlain impossible

-- Uninhabited (IsPlainCmd (DepCmd _ _)) where
--   uninhabited ItIsPlain impossible

-- Uninhabited (IsPlainCmd (ProdCmd _ _)) where
--   uninhabited ItIsPlain impossible

-- Uninhabited (IsPlainCmd (TDCmd _ _ _)) where
--   uninhabited ItIsPlain impossible

-- Uninhabited (IsPlainCmd (TPCmd _ _ _)) where
--   uninhabited ItIsPlain impossible

-- Uninhabited (IsPlainCmd (DPCmd _ _ _)) where
--   uninhabited ItIsPlain impossible

-- Uninhabited (IsPlainCmd (TDPCmd _ _  _ _)) where
--   uninhabited ItIsPlain impossible

-- ||| An edge in a Dependent State Automata, connecting two states by a command.
-- public export
-- data DSAEdge : Type where
--   MkDSAEdge :  (cmd  : DSALabel)
--             -> (from : Subset Value IsDataVal)
--             -> (to   : Subset Value IsDataVal)
--             -> DSAEdge

-- ||| A proof that an edge contains a plain command (i.e. carries no data).
-- public export
-- data IsPlainEdge : DSAEdge -> Type where
--   EdgeIsPlain : IsPlainEdge (MkDSAEdge (PlainCmd _) _ _)

-- Uninhabited (IsPlainEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
--   uninhabited EdgeIsPlain impossible

-- Uninhabited (IsPlainEdge (MkDSAEdge (DepCmd _ _) _ _)) where
--   uninhabited EdgeIsPlain impossible

-- Uninhabited (IsPlainEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
--   uninhabited EdgeIsPlain impossible

-- Uninhabited (IsPlainEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
--   uninhabited EdgeIsPlain impossible

-- Uninhabited (IsPlainEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
--   uninhabited EdgeIsPlain impossible

-- Uninhabited (IsPlainEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
--   uninhabited EdgeIsPlain impossible

-- Uninhabited (IsPlainEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
--   uninhabited EdgeIsPlain impossible

-- ||| Prove that the given edge is a plain edge, or produce a counter-proof for
-- ||| why it cannot be a plain edge.
-- isItPlainEdge : (edge : DSAEdge) -> Dec (IsPlainEdge edge)
-- isItPlainEdge (MkDSAEdge (PlainCmd _) _ _)     = Yes EdgeIsPlain
-- isItPlainEdge (MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
-- isItPlainEdge (MkDSAEdge (DepCmd _ _) _ _)     = No absurd
-- isItPlainEdge (MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
-- isItPlainEdge (MkDSAEdge (TDCmd _ _ _) _ _)    = No absurd
-- isItPlainEdge (MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
-- isItPlainEdge (MkDSAEdge (DPCmd _ _ _) _ _)    = No absurd
-- isItPlainEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _) = No absurd


-- public export
-- data UniversalEdge : Type where
--   MkUniversalEdge :  (cmd : Subset DSALabel IsPlainCmd)
--                   -> (to  : Subset Value IsDataVal)
--                   -> UniversalEdge

-- public export
-- data DSAv2 : Type where
--   MkDSAv2 :  (dsaName : String)
--           -> (states : Subset (List Value) (All IsDataVal))
--           -> {allEdges : List DSAEdge}
--           -> (edges : Split IsPlainEdge allEdges)
--           -> (universalEdges : List UniversalEdge)
--           -> DSAv2


-- ------------------------------------------------------------------------
-- -- dsa-gen Constraints.idr

-- --------------------
-- -- Take-edge only --
-- --------------------

-- public export
-- data IsTakeEdge : DSAEdge -> Type where
--   ItIsTakeEdge : IsTakeEdge (MkDSAEdge (TakeCmd _ _) _ _)

-- public export
-- Uninhabited (IsTakeEdge (MkDSAEdge (PlainCmd _) _ _)) where
--   uninhabited ItIsTakeEdge impossible
-- public export
-- Uninhabited (IsTakeEdge (MkDSAEdge (DepCmd _ _) _ _)) where
--   uninhabited ItIsTakeEdge impossible
-- public export
-- Uninhabited (IsTakeEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
--   uninhabited ItIsTakeEdge impossible
-- public export
-- Uninhabited (IsTakeEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
--   uninhabited ItIsTakeEdge impossible
-- public export
-- Uninhabited (IsTakeEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
--   uninhabited ItIsTakeEdge impossible
-- public export
-- Uninhabited (IsTakeEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
--   uninhabited ItIsTakeEdge impossible
-- public export
-- Uninhabited (IsTakeEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
--   uninhabited ItIsTakeEdge impossible

-- -------------------
-- -- Dep-edge only --
-- -------------------

-- public export
-- data IsDepEdge : DSAEdge -> Type where
--   ItIsDepEdge : IsDepEdge (MkDSAEdge (DepCmd _ _) _ _)

-- public export
-- Uninhabited (IsDepEdge (MkDSAEdge (PlainCmd _) _ _)) where
--   uninhabited ItIsDepEdge impossible
-- public export
-- Uninhabited (IsDepEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
--   uninhabited ItIsDepEdge impossible
-- public export
-- Uninhabited (IsDepEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
--   uninhabited ItIsDepEdge impossible
-- public export
-- Uninhabited (IsDepEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
--   uninhabited ItIsDepEdge impossible
-- public export
-- Uninhabited (IsDepEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
--   uninhabited ItIsDepEdge impossible
-- public export
-- Uninhabited (IsDepEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
--   uninhabited ItIsDepEdge impossible
-- public export
-- Uninhabited (IsDepEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
--   uninhabited ItIsDepEdge impossible

-- ||| Prove that an edge is a dependent edge (i.e. it contains a `DepCmd`), or
-- ||| produce a counter-proof for why it cannot be one.
-- public export
-- isDepEdge : (e : DSAEdge) -> Dec (IsDepEdge e)
-- isDepEdge e@(MkDSAEdge (DepCmd _ _) _ _)     = Yes ItIsDepEdge
-- isDepEdge e@(MkDSAEdge (PlainCmd _) _ _)     = No absurd
-- isDepEdge e@(MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
-- isDepEdge e@(MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
-- isDepEdge e@(MkDSAEdge (TDCmd _ _ _) _ _)    = No absurd
-- isDepEdge e@(MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
-- isDepEdge e@(MkDSAEdge (DPCmd _ _ _) _ _)    = No absurd
-- isDepEdge e@(MkDSAEdge (TDPCmd _ _ _ _) _ _) = No absurd

-- --------------------
-- -- Prod-edge only --
-- --------------------

-- public export
-- data IsProdEdge : DSAEdge -> Type where
--   ItIsProdEdge : IsProdEdge (MkDSAEdge (ProdCmd _ _) _ _)

-- public export
-- Uninhabited (IsProdEdge (MkDSAEdge (PlainCmd _) _ _)) where
--   uninhabited ItIsProdEdge impossible
-- public export
-- Uninhabited (IsProdEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
--   uninhabited ItIsProdEdge impossible
-- public export
-- Uninhabited (IsProdEdge (MkDSAEdge (DepCmd _ _) _ _)) where
--   uninhabited ItIsProdEdge impossible
-- public export
-- Uninhabited (IsProdEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
--   uninhabited ItIsProdEdge impossible
-- public export
-- Uninhabited (IsProdEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
--   uninhabited ItIsProdEdge impossible
-- public export
-- Uninhabited (IsProdEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
--   uninhabited ItIsProdEdge impossible
-- public export
-- Uninhabited (IsProdEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
--   uninhabited ItIsProdEdge impossible

-- ||| Prove that an edge is a producing edge (i.e. it contains a `ProdCmd`), or
-- ||| produce a counter-proof for why it cannot be one.
-- public export
-- isProdEdge : (e : DSAEdge) -> Dec (IsProdEdge e)
-- isProdEdge e@(MkDSAEdge (ProdCmd _ _) _ _)    = Yes ItIsProdEdge
-- isProdEdge e@(MkDSAEdge (PlainCmd _) _ _)     = No absurd
-- isProdEdge e@(MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
-- isProdEdge e@(MkDSAEdge (DepCmd _ _) _ _)     = No absurd
-- isProdEdge e@(MkDSAEdge (TDCmd _ _ _) _ _)    = No absurd
-- isProdEdge e@(MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
-- isProdEdge e@(MkDSAEdge (DPCmd _ _ _) _ _)    = No absurd
-- isProdEdge e@(MkDSAEdge (TDPCmd _ _ _ _) _ _) = No absurd

-- ------------------------
-- -- Take-dep edge only --
-- ------------------------

-- public export
-- data IsTDEdge : DSAEdge -> Type where
--   ItIsTDEdge : IsTDEdge (MkDSAEdge (TDCmd _ _ _) _ _)

-- public export
-- Uninhabited (IsTDEdge (MkDSAEdge (PlainCmd _) _ _)) where
--   uninhabited ItIsTDEdge impossible
-- public export
-- Uninhabited (IsTDEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
--   uninhabited ItIsTDEdge impossible
-- public export
-- Uninhabited (IsTDEdge (MkDSAEdge (DepCmd _ _) _ _)) where
--   uninhabited ItIsTDEdge impossible
-- public export
-- Uninhabited (IsTDEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
--   uninhabited ItIsTDEdge impossible
-- public export
-- Uninhabited (IsTDEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
--   uninhabited ItIsTDEdge impossible
-- public export
-- Uninhabited (IsTDEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
--   uninhabited ItIsTDEdge impossible
-- public export
-- Uninhabited (IsTDEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
--   uninhabited ItIsTDEdge impossible

-- ||| Prove that an edge is a take-dep edge (i.e. it contains a `TDCmd`), or
-- ||| produce a counter-proof for why it cannot be one.
-- public export
-- isTDEdge : (e : DSAEdge) -> Dec (IsTDEdge e)
-- isTDEdge e@(MkDSAEdge (TDCmd _ _ _) _ _)    = Yes ItIsTDEdge
-- isTDEdge e@(MkDSAEdge (PlainCmd _) _ _)     = No absurd
-- isTDEdge e@(MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
-- isTDEdge e@(MkDSAEdge (DepCmd _ _) _ _)     = No absurd
-- isTDEdge e@(MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
-- isTDEdge e@(MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
-- isTDEdge e@(MkDSAEdge (DPCmd _ _ _) _ _)    = No absurd
-- isTDEdge e@(MkDSAEdge (TDPCmd _ _ _ _) _ _) = No absurd

-- -------------------------
-- -- Take-prod edge only --
-- -------------------------

-- public export
-- data IsTPEdge : DSAEdge -> Type where
--   ItIsTPEdge : IsTPEdge (MkDSAEdge (TPCmd _ _ _) _ _)

-- public export
-- Uninhabited (IsTPEdge (MkDSAEdge (PlainCmd _) _ _)) where
--   uninhabited ItIsTPEdge impossible
-- public export
-- Uninhabited (IsTPEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
--   uninhabited ItIsTPEdge impossible
-- public export
-- Uninhabited (IsTPEdge (MkDSAEdge (DepCmd _ _) _ _)) where
--   uninhabited ItIsTPEdge impossible
-- public export
-- Uninhabited (IsTPEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
--   uninhabited ItIsTPEdge impossible
-- public export
-- Uninhabited (IsTPEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
--   uninhabited ItIsTPEdge impossible
-- public export
-- Uninhabited (IsTPEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
--   uninhabited ItIsTPEdge impossible
-- public export
-- Uninhabited (IsTPEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
--   uninhabited ItIsTPEdge impossible

-- ------------------------
-- -- Dep-prod edge only --
-- ------------------------

-- public export
-- data IsDPEdge : DSAEdge -> Type where
--   ItIsDPEdge : IsDPEdge (MkDSAEdge (DPCmd _ _ _) _ _)

-- public export
-- Uninhabited (IsDPEdge (MkDSAEdge (PlainCmd _) _ _)) where
--   uninhabited ItIsDPEdge impossible
-- public export
-- Uninhabited (IsDPEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
--   uninhabited ItIsDPEdge impossible
-- public export
-- Uninhabited (IsDPEdge (MkDSAEdge (DepCmd _ _) _ _)) where
--   uninhabited ItIsDPEdge impossible
-- public export
-- Uninhabited (IsDPEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
--   uninhabited ItIsDPEdge impossible
-- public export
-- Uninhabited (IsDPEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
--   uninhabited ItIsDPEdge impossible
-- public export
-- Uninhabited (IsDPEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
--   uninhabited ItIsDPEdge impossible
-- public export
-- Uninhabited (IsDPEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
--   uninhabited ItIsDPEdge impossible

-- ||| Prove that an edge is a dep-prod edge (i.e. it contains a `DPCmd`), or
-- ||| produce a counter-proof for why it cannot be one.
-- public export
-- isDPEdge : (e : DSAEdge) -> Dec (IsDPEdge e)
-- isDPEdge e@(MkDSAEdge (DPCmd _ _ _) _ _)    = Yes ItIsDPEdge
-- isDPEdge e@(MkDSAEdge (PlainCmd _) _ _)     = No absurd
-- isDPEdge e@(MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
-- isDPEdge e@(MkDSAEdge (DepCmd _ _) _ _)     = No absurd
-- isDPEdge e@(MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
-- isDPEdge e@(MkDSAEdge (TDCmd _ _ _) _ _)    = No absurd
-- isDPEdge e@(MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
-- isDPEdge e@(MkDSAEdge (TDPCmd _ _ _ _) _ _) = No absurd

-- -----------------------------
-- -- Take-dep-prod edge only --
-- -----------------------------

-- public export
-- data IsTDPEdge : DSAEdge -> Type where
--   ItIsTDPEdge : IsTDPEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)

-- public export
-- Uninhabited (IsTDPEdge (MkDSAEdge (PlainCmd _) _ _)) where
--   uninhabited ItIsTDPEdge impossible
-- public export
-- Uninhabited (IsTDPEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
--   uninhabited ItIsTDPEdge impossible
-- public export
-- Uninhabited (IsTDPEdge (MkDSAEdge (DepCmd _ _) _ _)) where
--   uninhabited ItIsTDPEdge impossible
-- public export
-- Uninhabited (IsTDPEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
--   uninhabited ItIsTDPEdge impossible
-- public export
-- Uninhabited (IsTDPEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
--   uninhabited ItIsTDPEdge impossible
-- public export
-- Uninhabited (IsTDPEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
--   uninhabited ItIsTDPEdge impossible
-- public export
-- Uninhabited (IsTDPEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
--   uninhabited ItIsTDPEdge impossible

-- ||| Prove that an edge is a take-dep-prod edge (i.e. it contains a `TDPCmd`), or
-- ||| produce a counter-proof for why it cannot be one.
-- public export
-- isTDPEdge : (e : DSAEdge) -> Dec (IsTDPEdge e)
-- isTDPEdge e@(MkDSAEdge (TDPCmd _ _ _ _) _ _) = Yes ItIsTDPEdge
-- isTDPEdge e@(MkDSAEdge (PlainCmd _) _ _)     = No absurd
-- isTDPEdge e@(MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
-- isTDPEdge e@(MkDSAEdge (DepCmd _ _) _ _)     = No absurd
-- isTDPEdge e@(MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
-- isTDPEdge e@(MkDSAEdge (TDCmd _ _ _) _ _)    = No absurd
-- isTDPEdge e@(MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
-- isTDPEdge e@(MkDSAEdge (DPCmd _ _ _) _ _)    = No absurd

-- -----------------------------
-- -- Non-depedent edges only --
-- -----------------------------

-- ||| A proof that a DSA-edge does not involve a dependent state change, i.e. is
-- ||| one of:
-- |||   - a ProdCmd
-- |||   - a TakeCmd
-- |||   - a TPCmd (take-prod)
-- public export
-- data IsNonDepEdge : DSAEdge -> Type where
--   ItIsProd : IsNonDepEdge (MkDSAEdge (ProdCmd _ _) _ _)
--   ItIsTake : IsNonDepEdge (MkDSAEdge (TakeCmd _ _) _ _)
--   ItIsTP   : IsNonDepEdge (MkDSAEdge (TPCmd _ _ _) _ _)

-- ||| A `DepCmd` IS a DepEdge
-- public export
-- Uninhabited (IsNonDepEdge (MkDSAEdge (DepCmd _ _) _ _)) where
--   uninhabited ItIsProd impossible
--   uninhabited ItIsTake impossible
--   uninhabited ItIsTP impossible

-- ||| A `TDCmd` (take-dep) IS a DepEdge
-- public export
-- Uninhabited (IsNonDepEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
--   uninhabited ItIsProd impossible
--   uninhabited ItIsTake impossible
--   uninhabited ItIsTP impossible

-- ||| A `DPCmd` (dep-prod) IS a DepEdge
-- public export
-- Uninhabited (IsNonDepEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
--   uninhabited ItIsProd impossible
--   uninhabited ItIsTake impossible
--   uninhabited ItIsTP impossible

-- ||| A `TDPCmd` (take-dep-prod) IS a DepEdge
-- public export
-- Uninhabited (IsNonDepEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
--   uninhabited ItIsProd impossible
--   uninhabited ItIsTake impossible
--   uninhabited ItIsTP impossible

-- --------------------------------------
-- -- Non-plain AND non-dependent only --
-- --------------------------------------

-- ||| A proof that the given edge is not a dependent edge (i.e. it always goes to
-- ||| the same state), AND that the edge is not a plain edge (i.e. it _does_ do
-- ||| something interesting, for example producing a value).
-- ||| Second attempt at `NotPlainNonDep`...
-- public export
-- data NPND : Subset DSAEdge (Not . IsPlainEdge) -> Type where
--   ProdNonDep : NPND (Element (MkDSAEdge (ProdCmd _ _) _ _) nonPlainPrf)
--   TakeNonDep : NPND (Element (MkDSAEdge (TakeCmd _ _) _ _) nonPlainPrf)
--   TPNonDep   : NPND (Element (MkDSAEdge (TPCmd _ _ _) _ _) nonPlainPrf)

-- public export
-- Uninhabited (NPND (Element (MkDSAEdge (DepCmd _ _) _ _) nonPlainPrf)) where
--   uninhabited ProdNonDep impossible
--   uninhabited TakeNonDep impossible
--   uninhabited TPNonDep impossible

-- public export
-- Uninhabited (NPND (Element (MkDSAEdge (TDCmd _ _ _) _ _) nonPlainPrf)) where
--   uninhabited ProdNonDep impossible
--   uninhabited TakeNonDep impossible
--   uninhabited TPNonDep impossible

-- public export
-- Uninhabited (NPND (Element (MkDSAEdge (DPCmd _ _ _) _ _) nonPlainPrf)) where
--   uninhabited ProdNonDep impossible
--   uninhabited TakeNonDep impossible
--   uninhabited TPNonDep impossible

-- public export
-- Uninhabited (NPND (Element (MkDSAEdge (TDPCmd _ _ _ _) _ _) nonPlainPrf)) where
--   uninhabited ProdNonDep impossible
--   uninhabited TakeNonDep impossible
--   uninhabited TPNonDep impossible

-- -------------------
-- -- Dec functions --
-- -------------------

-- public export
-- isNPND : (s : Subset DSAEdge (Not . IsPlainEdge)) -> Dec (NPND s)
-- isNPND (Element (MkDSAEdge (PlainCmd _) _ _) snd)     = void $ snd EdgeIsPlain
-- isNPND (Element (MkDSAEdge (DepCmd _ _) _ _) snd)     = No absurd
-- isNPND (Element (MkDSAEdge (TDCmd _ _ _) _ _) snd)    = No absurd
-- isNPND (Element (MkDSAEdge (DPCmd _ _ _) _ _) snd)    = No absurd
-- isNPND (Element (MkDSAEdge (TDPCmd _ _ _ _) _ _) snd) = No absurd
-- isNPND (Element (MkDSAEdge (TakeCmd _ _) _ _) snd)    = Yes TakeNonDep
-- isNPND (Element (MkDSAEdge (ProdCmd _ _) _ _) snd)    = Yes ProdNonDep
-- isNPND (Element (MkDSAEdge (TPCmd _ _ _) _ _) snd)    = Yes TPNonDep

-- -- %runElab deriveDecEq Value
-- -- %runElab deriveDecEq TakeArg
-- -- %runElab deriveDecEq DepArg
-- -- %runElab deriveDecEq ProdArg
-- -- %runElab deriveDecEq DSALabel
-- -- %runElab deriveDecEq IsDataVal
-- -- %runElab deriveDecEq IsPlainCmd
-- -- %runElab deriveDecEq DSAEdge
-- -- %runElab deriveDecEq IsPlainEdge
-- -- %runElab deriveDecEq UniversalEdge
-- -- %runElab deriveDecEq DSAv2
-- -- %runElab deriveDecEq IsTakeEdge
-- -- %runElab deriveDecEq IsDepEdge
-- -- %runElab deriveDecEq IsProdEdge
-- -- %runElab deriveDecEq IsTDEdge
-- -- %runElab deriveDecEq IsTPEdge
-- -- %runElab deriveDecEq IsDPEdge
-- -- %runElab deriveDecEq IsTDPEdge
-- -- %runElab deriveDecEq IsNonDepEdge
-- -- %runElab deriveDecEq NPND

-- -- decEq : (t_x1, t_x2 : Value) -> Dec (t_x1 === t_x2)

-- -- DecEq Value where
-- --   decEq (IdrName n1) (IdrName n2) with (decEq n1 n2) 
-- --       decEq (IdrName n1) (IdrName n1) | (Yes Refl) = Yes Refl
-- --       decEq (IdrName n1) (IdrName n2) | (No prf) = No (\ h => prf (case h of Refl => Refl )) 
-- --   decEq (IdrName n1) (LitVal lit2) = No (\ h => case h of Refl impossible )
-- --   decEq (IdrName n1) (DataVal dc2 args2) = No (\ h => case h of Refl impossible )
-- --   decEq (IdrName n1) (AddExpr num2 addend2) = No (\ h => case h of Refl impossible)
-- --   decEq (IdrName n1) (Tuple fst2 snd2) = No (\ h => case h of Refl impossible )
-- --   decEq (LitVal lit1) (IdrName n2) = No (\ h => case h of Refl impossible )
-- --   decEq (LitVal lit1) (LitVal lit2) with (decEq lit1 lit2) 
-- --       decEq (LitVal lit1) (LitVal lit1) | (Yes Refl) = Yes Refl
-- --       decEq (LitVal lit1) (LitVal lit2) | (No prf) = No (\ h => prf (case h of Refl => Refl )) 
-- --   decEq (LitVal lit1) (DataVal dc2 args2) = No (\ h => case h of Refl impossible )
-- --   decEq (LitVal lit1) (AddExpr num2 addend2) = No (\ h => case h of Refl impossible )
-- --   decEq (LitVal lit1) (Tuple fst2 snd2) = No (\ h => case h of Refl impossible )
-- --   decEq (DataVal dc1 args1) (IdrName n2) = No (\ h => case h of Refl impossible )
-- --   decEq (DataVal dc1 args1) (LitVal lit2) = No (\ h => case h of Refl impossible )
-- --   decEq (DataVal dc1 args1) (DataVal dc2 args2) with (decEq dc1 dc2) 
-- --       decEq (DataVal dc1 args1) (DataVal dc1 args2) | (Yes Refl) with (decEq args1 args2) 
-- --           decEq (DataVal dc1 args1) (DataVal dc1 args1) | (Yes Refl) | (Yes Refl) = Yes Refl
-- --           decEq (DataVal dc1 args1) (DataVal dc1 args2) | (Yes Refl) | (No prf) = No (\ h => prf (case h of Refl => Refl )) 
-- --       decEq (DataVal dc1 args1) (DataVal dc2 args2) | (No prf) = No (\ h => prf (case h of  Refl => Refl )) 
-- --   decEq (DataVal dc1 args1) (AddExpr num2 addend2) = No (\ h => case h of Refl impossible )
-- --   decEq (DataVal dc1 args1) (Tuple fst2 snd2) = No (\ h => case h of Refl impossible )
-- --   decEq (AddExpr num1 addend1) (IdrName n2) = No (\ h => case h of Refl impossible )
-- --   decEq (AddExpr num1 addend1) (LitVal lit2) = No (\ h => case h of Refl impossible )
-- --   decEq (AddExpr num1 addend1) (DataVal dc2 args2) = No (\ h => case h of Refl impossible )
-- --   decEq (AddExpr num1 addend1) (AddExpr num2 addend2) with (decEq num1 num2) 
-- --       decEq (AddExpr num1 addend1) (AddExpr num1 addend2) | (Yes Refl) with (decEq addend1 addend2) 
-- --           decEq (AddExpr num1 addend1) (AddExpr num1 addend1) | (Yes Refl) | (Yes Refl) = Yes Refl
-- --           decEq (AddExpr num1 addend1) (AddExpr num1 addend2) | (Yes Refl) | (No prf) = No (\ h => prf (case h of Refl => Refl )) 
-- --       decEq (AddExpr num1 addend1) (AddExpr num2 addend2) | (No prf) = No (\ h => prf (case h of Refl => Refl )) 
-- --   decEq (AddExpr num1 addend1) (Tuple fst2 snd2) = No (\ h => case h of Refl impossible )
-- --   decEq (Tuple fst1 snd1) (IdrName n2) = No (\ h => case h of Refl impossible )
-- --   decEq (Tuple fst1 snd1) (LitVal lit2) = No (\ h => case h of Refl impossible )
-- --   decEq (Tuple fst1 snd1) (DataVal dc2 args2) = No (\ h => case h of Refl impossible )
-- --   decEq (Tuple fst1 snd1) (AddExpr num2 addend2) = No (\ h => case h of Refl impossible )
-- --   decEq (Tuple fst1 snd1) (Tuple fst2 snd2) with (decEq fst1 fst2) 
-- --       decEq (Tuple fst1 snd1) (Tuple fst1 snd2) | (Yes Refl) with (decEq snd1 snd2) 
-- --           decEq (Tuple fst1 snd1) (Tuple fst1 snd1) | (Yes Refl) | (Yes Refl) = Yes Refl
-- --           decEq (Tuple fst1 snd1) (Tuple fst1 snd2) | (Yes Refl) | (No prf) = No (\ h => prf (case h of Refl => Refl )) 
-- --       decEq (Tuple fst1 snd1) (Tuple fst2 snd2) | (No prf) = No (\ h => prf (case h of Refl => Refl )) 


-- -- data Test : Type where
-- --   Base : Test 
-- --   Ind : Test -> Maybe Test -> Test 

-- -- DecEq Test where
-- --   decEq Base Base = Yes Refl 
-- --   decEq Base (Ind _ _) = No (\h => case h of Refl impossible)
-- --   decEq (Ind _ _) Base = No (\h => case h of Refl impossible)
-- --   decEq (Ind x y) (Ind a b) with (decEq x a) 
-- --     decEq (Ind x y) (Ind x b) | Yes Refl with (decEq y b)
-- --       decEq (Ind x y) (Ind x y) | Yes Refl | Yes Refl = Yes Refl 
-- --       decEq (Ind x y) (Ind x b) | Yes Refl | No prf = No (\h => prf (case h of Refl => Refl))
-- --     decEq (Ind x y) (Ind a b) | No prf = No (\h => prf (case h of Refl => Refl))

-- -- data Test2 : Type where
-- --   Base : Test2
-- --   Ind : Maybe Test2 -> Test2

-- -- DecEq Test2 where
-- --   decEq Base Base = Yes Refl
-- --   decEq Base (Ind _) = No (\h => case h of Refl impossible)
-- --   decEq (Ind _) Base = No (\h => case h of Refl impossible)
-- --   decEq (Ind (Just x)) (Ind (Just y)) with (decEq x y)
-- --     decEq (Ind (Just x)) (Ind (Just x)) | Yes Refl = Yes Refl
-- --     decEq (Ind (Just x)) (Ind (Just y)) | No prf = No (\h => prf (case h of Refl => Refl ))
-- --   decEq (Ind Nothing) (Ind (Just y)) = No (\h => case h of Refl impossible)
-- --   decEq (Ind (Just x)) (Ind Nothing) = No (\h => case h of Refl impossible)
-- --   decEq (Ind Nothing) (Ind Nothing) = Yes Refl

-- -- DecEq Test2 where
-- --   decEq Base Base = Yes Refl
-- --   decEq Base (Ind _) = No (\h => case h of Refl impossible)
-- --   decEq (Ind _) Base = No (\h => case h of Refl impossible)
-- --   decEq (Ind x) (Ind y) with (decEq x y)
-- --     decEq (Ind x) (Ind x) | Yes Refl = Yes Refl
-- --     decEq (Ind x) (Ind y) | No prf = No (\h => prf (case h of Refl => Refl ))