From Coq Require Import ZArith.BinInt Lists.List Strings.String.

Import ListNotations.

From Poulet4 Require Import Utils.AList P4light.Syntax.Syntax Utils.ForallMap.

From Poulet4.P4light.Syntax Require P4String P4Int Typed.

Section Value.

Inductive ValueBase {bit : Type} :=
  | ValBaseNull
  | ValBaseBool (_: bit)
  | ValBaseInteger (_: Z)
  | ValBaseBit (value: list bit)
  | ValBaseInt (value: list bit)
  | ValBaseVarbit (max: N) (value: list bit)
  | ValBaseString (_: string)
  | ValBaseTuple (_: list (@ValueBase bit))
  | ValBaseError (_: string)
  | ValBaseMatchKind (_: string)
  | ValBaseStruct (fields: StringAList (@ValueBase bit))
  | ValBaseHeader (fields: StringAList (@ValueBase bit)) (is_valid: bit)
  | ValBaseUnion (fields: StringAList (@ValueBase bit))
  | ValBaseStack (headers: list (@ValueBase bit)) (next: N)
  | ValBaseEnumField (typ_name: string) (enum_name: string)
  | ValBaseSenumField (typ_name: string) (value: (@ValueBase bit)).

Inductive ValueLvalue :=
  | ValLeftName (loc: Syntax.Locator)
  | ValLeftMember (expr: ValueLvalue) (name: string)
  | ValLeftBitAccess (expr: ValueLvalue) (msb: N) (lsb: N)
  | ValLeftArrayAccess (expr: ValueLvalue) (idx: Z).

Inductive ValueSet:=
  | ValSetSingleton (value: (@ValueBase bool))
  | ValSetUniversal
  | ValSetMask (value: (@ValueBase bool)) (mask: (@ValueBase bool))
  | ValSetRange (lo: (@ValueBase bool)) (hi: (@ValueBase bool))
  | ValSetProd (_: list ValueSet)
  | ValSetLpm (nbits: N) (value: (@ValueBase bool))
  | ValSetValueSet (size: N) (members: list (list ValueSet)) (sets: list ValueSet).

Definition ValueLoc := string.

Context {tags_t : Type}.

Inductive ValueTable :=
  | MkValTable (name: string) (keys: list (@Syntax.TableKey tags_t))
               (actions: list (@Syntax.TableActionRef tags_t))
               (default_action: @Syntax.TableActionRef tags_t)
               (const_entries: list (@Syntax.TableEntry tags_t)).

Definition Env_env binding := list (StringAList binding).

Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (vs: Env_env ValueLoc) (typ: Env_env (@Typed.P4Type tags_t)) (namespace: string).

Inductive ValueFunctionImplementation :=
  | ValFuncImplUser (scope: Env_EvalEnv) (body: (@Syntax.Block tags_t))
  | ValFuncImplExtern (name: string) (caller: option (ValueLoc * string))
  | ValFuncImplBuiltin (name: string) (caller: ValueLvalue).

Inductive ValueObject :=
  | ValObjParser (scope: Env_EvalEnv)
                 (constructor_params: list (@Typed.P4Parameter tags_t))
                 (params: list (@Typed.P4Parameter tags_t)) (locals: list (@Syntax.Declaration tags_t))
                 (states: list (@Syntax.ParserState tags_t))
  | ValObjTable (_: ValueTable)
  | ValObjControl (scope: Env_EvalEnv)
                  (constructor_params: list (@Typed.P4Parameter tags_t))
                  (params: list (@Typed.P4Parameter tags_t)) (locals: list (@Syntax.Declaration tags_t))
                  (apply: (@Syntax.Block tags_t))
  | ValObjPackage (args: StringAList ValueLoc)
  | ValObjRuntime (loc: ValueLoc) (obj_name: string)
  | ValObjFun (params: list (@Typed.P4Parameter tags_t)) (impl: ValueFunctionImplementation)
  | ValObjAction (scope: Env_EvalEnv) (params: list (@Typed.P4Parameter tags_t))
                 (body: (@Syntax.Block tags_t))
  | ValObjPacket (bits: list bool).

Inductive ValueConstructor :=
  | ValConsParser (scope: Env_EvalEnv) (constructor_params: list (@Typed.P4Parameter tags_t))
                  (params: list (@Typed.P4Parameter tags_t)) (locals: list (@Syntax.Declaration tags_t))
                  (states: list (@Syntax.ParserState tags_t))
  | ValConsTable (_: ValueTable)
  | ValConsControl (scope: Env_EvalEnv) (constructor_params: list (@Typed.P4Parameter tags_t))
                   (params: list (@Typed.P4Parameter tags_t)) (locals: list (@Syntax.Declaration tags_t))
                   (apply: (@Syntax.Block tags_t))
  | ValConsPackage (params: list (@Typed.P4Parameter tags_t)) (args: StringAList ValueLoc)
  | ValConsExternObj (_: StringAList (list (@Typed.P4Parameter tags_t))).

Inductive Value (bit : Type) :=
  | ValBase (_: @ValueBase bit)
  | ValObj (_: ValueObject)
  | ValCons (_: ValueConstructor).

Section ValBaseInd.

Variable bit : Type.

Notation V := (@ValueBase bit).

Variable P : V -> Prop.

Hypothesis HNull : P ValBaseNull.
Hypothesis HBool : forall b, P (ValBaseBool b).
Hypothesis HInteger : forall z, P (ValBaseInteger z).
Hypothesis HBit : forall n, P (ValBaseBit n).
Hypothesis HInt : forall z, P (ValBaseInt z).
Hypothesis HVarbit : forall w n, P (ValBaseVarbit w n).
Hypothesis HString : forall s, P (ValBaseString s).
Hypothesis HTuple : forall vs,
    Forall P vs -> P (ValBaseTuple vs).
Hypothesis HError : forall err, P (ValBaseError err).
Hypothesis HMatchKind : forall mk, P (ValBaseMatchKind mk).
Hypothesis HStruct : forall vs,
    Forall (fun '(_,v) => P v) vs -> P (ValBaseStruct vs).
Hypothesis HHeader : forall vs b,
    Forall (fun '(_,v) => P v) vs -> P (ValBaseHeader vs b).
Hypothesis HUnion : forall vs,
    Forall (fun '(_,v) => P v) vs -> P (ValBaseUnion vs).
Hypothesis HStack : forall vs i,
    Forall P vs -> P (ValBaseStack vs i).
Hypothesis HEnumField : forall t x, P (ValBaseEnumField t x).
Hypothesis HSenumField : forall t v,
    P v -> P (ValBaseSenumField t v).

Definition custom_ValueBase_ind :
      forall v : V, P v :=
      fix vind (v : V) : P v :=
        let fix lind (vs : list V) : Forall P vs :=
            match vs with
            | []     => Forall_nil _
            | v :: vs => Forall_cons _ (vind v) (lind vs)
            end in
        let fix alind (vs : AList.AList _ V _) : Forall (fun '(_,v) => P v) vs :=
            match vs with
            | []          => Forall_nil _
            | (_,v) as xv :: vs => Forall_cons xv (vind v) (alind vs)
            end in
        match v with
        | ValBaseNull             => HNull
        | ValBaseBool b           => HBool b
        | ValBaseInteger z        => HInteger z
        | ValBaseBit n            => HBit n
        | ValBaseInt z            => HInt z
        | ValBaseVarbit w n       => HVarbit w n
        | ValBaseString s         => HString s
        | ValBaseTuple vs         => HTuple _ (lind vs)
        | ValBaseError err        => HError err
        | ValBaseMatchKind mk     => HMatchKind mk
        | ValBaseStruct vs        => HStruct _ (alind vs)
        | ValBaseHeader vs b      => HHeader _ b (alind vs)
        | ValBaseUnion vs         => HUnion _ (alind vs)
        | ValBaseStack vs i       => HStack _ i (lind vs)
        | ValBaseEnumField t x    => HEnumField t x
        | ValBaseSenumField t v   => HSenumField t _ (vind v)
        end.

End ValBaseInd.

Section ValueSetInd.

Variable P : ValueSet -> Prop.

Hypothesis HSingleton : forall value, P (ValSetSingleton value).
Hypothesis HUniversal : P ValSetUniversal.
Hypothesis HMask : forall value mask, P (ValSetMask value mask).
Hypothesis HRange : forall lo hi, P (ValSetRange lo hi).
Hypothesis HProd : forall l, Forall P l -> P (ValSetProd l).
Hypothesis HLpm : forall nbits value, P (ValSetLpm nbits value).
Hypothesis HValueSet :
  forall size members sets,
    Forall (Forall P) members -> Forall P sets -> P (ValSetValueSet size members sets).

Fixpoint custom_ValueSet_ind (v : ValueSet) : P v :=
      let fix list_ind (vs : list ValueSet) : Forall P vs :=
        match vs with
        | v :: vs => Forall_cons _ (custom_ValueSet_ind v) (list_ind vs)
        | [] => Forall_nil _
        end
      in
      let fix nested_list_ind (vs : list (list ValueSet)) : Forall (Forall P) vs :=
        match vs with
        | v :: vs => Forall_cons _ (list_ind v) (nested_list_ind vs)
        | [] => Forall_nil _
        end
      in
      match v with
      | ValSetSingleton value => HSingleton value
      | ValSetUniversal => HUniversal
      | ValSetMask value mask => HMask value mask
      | ValSetRange lo hi => HRange lo hi
      | ValSetProd l => HProd _ (list_ind l)
      | ValSetLpm nbits value => HLpm nbits value
      | ValSetValueSet _ members sets =>
        HValueSet _ _ _ (nested_list_ind members) (list_ind sets)
      end.

End ValueSetInd.

Section ValueBaseFunctor.

Context {A B : Type}.

Variable (f : A -> B).

Fixpoint ValueBaseMap (v : @ValueBase A) : @ValueBase B :=
      match v with
      | ValBaseNull         => ValBaseNull
      | ValBaseInteger z    => ValBaseInteger z
      | ValBaseString s     => ValBaseString s
      | ValBaseError e      => ValBaseError e
      | ValBaseMatchKind mk => ValBaseMatchKind mk
      | ValBaseBool a       => ValBaseBool (f a)
      | ValBaseBit n        => ValBaseBit (map f n)
      | ValBaseInt z        => ValBaseInt (map f z)
      | ValBaseVarbit w n   => ValBaseVarbit w (map f n)
      | ValBaseTuple vs     => ValBaseTuple (map ValueBaseMap vs)
      | ValBaseStruct vs    =>
        ValBaseStruct (map (fun '(x,v) => (x, ValueBaseMap v)) vs)
      | ValBaseHeader vs a  =>
        ValBaseHeader (map (fun '(x,v) => (x, ValueBaseMap v)) vs) (f a)
      | ValBaseUnion vs     =>
        ValBaseUnion (map (fun '(x,v) => (x, ValueBaseMap v)) vs)
      | ValBaseStack vs i =>
        ValBaseStack (map ValueBaseMap vs) i
      | ValBaseEnumField t x => ValBaseEnumField t x
      | ValBaseSenumField t v => ValBaseSenumField t (ValueBaseMap v)
      end.

End ValueBaseFunctor.

Inductive signal : Type :=
 | SContinue : signal
 | SReturn : (@ValueBase bool) -> signal
 | SExit

 | SReject : string -> signal.

Definition SReturnNull := SReturn ValBaseNull.

End Value.
