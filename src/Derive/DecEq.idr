module Derive.DecEq

import Language.Reflection.Util 
import Decidable.Equality
import Language.Reflection.Pretty
import Language.Reflection.Syntax.Ops
import Language.Reflection
import Data.Vect

%default total
%language ElabReflection

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
            findf x = (\e => (dropNS (fromString x) == (dropNS e.name)) || (e.name == fromString x)) in
                case (find (findf x) ti.cons, find (findf y) ti.cons) of 
                    (Just x', Just y') => (::) <$> pure (x', y') <*> (strToCons xs)
                    (_, _) => fail "error: names dont match :("

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
    logMsg "auto" 1 $ show impl 
    declare [interfaceHint Public fName clHint, def fName [var fName .= impl ]]
