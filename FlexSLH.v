(** * FlexSLH: Selective Ultimate SLH *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From SECF Require Import TestingSpecCT.
(* From SECF Require Import UltimateSLH. *)
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(* Tail recursive append to prevent stack overflows when testing *)
Fixpoint rev_append {A:Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: l1 => rev_append l1 (x :: l2)
  end.
Definition rev {A : Type} (l : list A) := rev_append l [].
Definition app {A:Type} (l1:list A) := rev_append (rev l1).
Notation "x ++ y" := (app x y) (right associativity, at level 60).

Fixpoint vars_aexp (a:aexp) : list string :=
  match a with
  | ANum n => []
  | AId (Var i) => [i]
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => vars_aexp a1 ++ vars_aexp a2
  | <{ be ? a1 : a2 }> => vars_bexp be ++ vars_aexp a1 ++ vars_aexp a2
  end
with vars_bexp (a:bexp) : list string :=
  match a with
  | <{ true }> | <{ false }> => []
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => vars_aexp a1 ++ vars_aexp a2
  | <{ ~b }> => vars_bexp b
  | <{ b1 && b2 }> => vars_bexp b1 ++ vars_bexp b2
  end.

Definition label_of_aexp (P:pub_vars) (a:aexp) : label :=
  List.fold_left (fun l a => join l (apply P a)) (vars_aexp a) public.

Definition label_of_bexp (P:pub_vars) (b:bexp) : label :=
  List.fold_left (fun l b => join l (apply P b)) (vars_bexp b) public.

Lemma no_vars_public_bexp : forall P b,
  seq.nilp (vars_bexp b) = true ->
  label_of_bexp P b = public.
Proof. intros P b H. unfold label_of_bexp. destruct (vars_bexp b); eauto. Qed.

Lemma no_vars_public_aexp : forall P a,
  seq.nilp (vars_aexp a) = true ->
  label_of_aexp P a = public.
Proof. intros P a H. unfold label_of_aexp. destruct (vars_aexp a); eauto. Qed.

Definition AllPub : pub_vars := (_!-> public).
Definition AllSecret : pub_vars := (_!-> secret).

Lemma joining_to_secret : forall l' (xs:list string),
  List.fold_left (fun l b => join l l') xs secret = secret.
Proof. intros P xs. induction xs; eauto. Qed.

Lemma all_secret_bexp : forall b,
  seq.nilp (vars_bexp b) = false ->
  label_of_bexp AllSecret b = secret.
Proof.
  intros b H. unfold label_of_bexp. destruct (vars_bexp b) eqn:Eq; eauto.
  simpl. apply joining_to_secret.
Qed.

Lemma all_secret_aexp : forall a,
  seq.nilp (vars_aexp a) = false ->
  label_of_aexp AllSecret a = secret.
Proof.
  intros a H. unfold label_of_aexp. destruct (vars_aexp a) eqn:Eq; eauto.
  simpl. apply joining_to_secret.
Qed.

Fixpoint flex_slh (P:pub_vars) (c:com) : com :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ flex_slh P c1; flex_slh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      if label_of_bexp P be
      then (* Selective SLH -- tracking speculation, but not masking *)
        <{{if be then "b" := be ? "b" : 1; flex_slh P c1
                 else "b" := be ? 1 : "b"; flex_slh P c2 end}}>
      else (* Ultimate SLH -- tracking speculation and also masking *)
        <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; flex_slh P c1
                            else "b" := ("b" = 0 && be) ? 1 : "b"; flex_slh P c2 end}}>
  | <{{while be do c end}}> =>
      if label_of_bexp P be
      then (* Selective SLH -- tracking speculation, but not masking *)
        <{{while be do "b" := be ? "b" : 1; flex_slh P c end;
           "b" := be ? 1 : "b"}}>
      else (* Ultimate SLH -- tracking speculation and also masking *)
        <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; flex_slh P c end;
           "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    if label_of_aexp P i
    then (* Selective SLH -- mask the value of public loads *)
      if apply P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
                   else <{{x <- a[[i]]}}>
    else (* Ultimate SLH -- mask private address of load *)
      <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> =>
    if label_of_aexp P i
    then (* Selective SLH *)
      <{{a[i] <- e}}> (* <- Doing nothing here okay for Spectre v1,
         but problematic for return address or code pointer overwrites *)
    else (* Ultimate SLH *)
      <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

(* For CT programs this is the same as sel_slh *)

Ltac rewrite_eq :=
  match goal with
  | H:_=_ |- _ => rewrite H; clear H
  | H:forall _, _=_ |- _ => rewrite H; clear H
  | _ => idtac
 end.

Module RelatingSelSLH.

  Lemma label_of_aexp_sound : forall P a,
    P |-a- a \IN label_of_aexp P a.
  Admitted.

  Lemma label_of_aexp_unique : forall P a l,
    P |-a- a \IN l ->
    l = label_of_aexp P a.
  Admitted.

  Lemma label_of_bexp_sound : forall P b,
    P |-b- b \IN label_of_bexp P b.
  Admitted.

  Lemma label_of_bexp_unique : forall P b l,
    P |-b- b \IN l ->
    l = label_of_bexp P b.
  Admitted.

  Lemma sel_slh_is_flex_slh : forall P PA c,
      ct_well_typed P PA c ->
      sel_slh P c = flex_slh P c.
  Proof.
    intros P PA c H. induction H; simpl; repeat rewrite_eq; try reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. reflexivity.
  Qed.

End RelatingSelSLH.

(* The following standard IFC type system that just tracks explicit and implicit
   flows seems good enough for what we need. Most importantly, it gives us
   noninterference both sequentially and speculatively after applying flex_slh
   (see testing below). *)

Reserved Notation "P '&' PA ',' pc '|--' c" (at level 40).

Inductive well_typed (P PA : pub_vars) : label -> com -> Prop :=
  | WT_Com : forall pc,
      P & PA, pc |-- <{ skip }>
  | WT_Asgn : forall pc X a l,
      P |-a- a \IN l ->
      can_flow (join pc l) (apply P X) = true ->
      P & PA, pc |-- <{ X := a }>
  | WT_Seq : forall pc c1 c2,
      P & PA, pc |-- c1 ->
      P & PA, pc |-- c2 ->
      P & PA, pc |-- <{ c1 ; c2 }>
  | WT_If : forall pc b l c1 c2,
      P |-b- b \IN l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, (join pc l) |-- c2 ->
      P & PA, pc |-- <{ if b then c1 else c2 end }>
  | WT_While : forall pc b l c1,
      P |-b- b \IN l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, pc |-- <{ while b do c1 end }>
  | WT_ARead : forall pc x a i li,
      P |-a- i \IN li ->
      can_flow (join pc (join li (apply PA a))) (apply P x) = true ->
      P & PA, pc |-- <{{ x <- a[[i]] }}>
  | WT_AWrite : forall pc a i e li l,
      P |-a- i \IN li ->
      P |-a- e \IN l ->
      can_flow (join pc (join li l)) (apply PA a) = true ->
      P & PA, pc |-- <{{ a[i] <- e }}>
where "P '&' PA ',' pc '|--' c" := (well_typed P PA pc c).

Definition nonempty_arrs (ast :astate) :Prop :=
  forall a, 0 < length (apply ast a).

Definition seq_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2,
    <(st1, ast1)> =[ c ]=> <(stt1, astt1, os1)> ->
    <(st2, ast2)> =[ c ]=> <(stt2, astt2, os2)> ->
    os1 = os2.

Definition spec_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure trans c st1 st2 ast1 ast2 : Prop :=
  seq_same_obs c st1 st2 ast1 ast2 ->
  spec_same_obs (trans c) st1 st2 ast1 ast2.

Definition ct_preservation trans : Prop := forall c,
  (forall st1 st2 ast1 ast2, seq_same_obs c st1 st2 ast1 ast2) ->
  (forall st1 st2 ast1 ast2, spec_same_obs (trans c) st1 st2 ast1 ast2).

Theorem relative_secure_implies_ct_preservation : forall trans,
  (forall c st1 st2 ast1 ast2, relative_secure trans c st1 st2 ast1 ast2) ->
  ct_preservation trans.
Proof.
  unfold relative_secure, ct_preservation.
  intros trans Hrs c Hct st1 st2 ast1 ast2. apply Hrs. apply Hct.
Qed.

(* The converse is generally not true *)
Lemma not_true_that_ct_preservation_implies_relative_secure : forall trans,
  ct_preservation trans ->
  (forall c st1 st2 ast1 ast2, relative_secure trans c st1 st2 ast1 ast2).
Proof.
  unfold relative_secure, ct_preservation.
  intros trans H c st1 st2 ast1 ast2 Hsrc. apply H. intros st1' st2' ast1' ast2'.
Abort.

Conjecture flex_slh_relative_secure :
  forall P PA c st1 st2 ast1 ast2,
    (* Selective SLH assumptions *)
    P & PA, public |-- c -> (* just that this is weaker (not ct_well_typed) *)
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    (* Joint assumptions *)
    unused "b" c ->
    apply st1 "b" = 0 ->
    apply st2 "b" = 0 ->
    (* Ultimate SLH assumptions  *)
    nonempty_arrs ast1 ->
    nonempty_arrs ast2 ->
    relative_secure (flex_slh P) c st1 st2 ast1 ast2.

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import String.

Notation label := TestingSpecCT.label.
Notation apply := TestingSpecCT.apply.
Notation join := TestingSpecCT.join.

Fixpoint wt_typechecker (P PA:pub_vars) (pc:label) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (join pc (label_of_aexp P a)) (apply P X)
  | <{ c1 ; c2 }> => wt_typechecker P PA pc c1 && wt_typechecker P PA pc c2
  | <{ if b then c1 else c2 end }> =>
      wt_typechecker P PA (join pc (label_of_bexp P b)) c1 &&
      wt_typechecker P PA (join pc (label_of_bexp P b)) c2
  | <{ while b do c1 end }> =>
      wt_typechecker P PA (join pc (label_of_bexp P b)) c1
  | <{{ x <- a[[i]] }}> =>
      can_flow (join pc (join (label_of_aexp P i) (apply PA a))) (apply P x)
  | <{{ a[i] <- e }}> =>
      can_flow (join pc (join (label_of_aexp P i) (label_of_aexp P e))) (apply PA a)
  end.

Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Definition gen_pub_aexp_leaf (P : pub_vars) : G aexp :=
  oneOf (liftM ANum arbitrary ;;;
         (let pubs := map Var (filter (apply P) (map_dom (snd P))) in
         if seq.nilp pubs then []
         else [liftM AId (elems_ (Var "X0"%string) pubs)] ) ).

Fixpoint gen_pub_aexp (sz:nat) (P:pub_vars) : G aexp :=
  match sz with
  | O => thunkGen (fun _ => gen_pub_aexp_leaf P)
  | S sz' =>
      freq [ (3, thunkGen (fun _ => gen_pub_aexp_leaf P));
             (sz, thunkGen (fun _ => liftM2 APlus (gen_pub_aexp sz' P) (gen_pub_aexp sz' P)));
             (sz, thunkGen (fun _ => liftM2 AMinus (gen_pub_aexp sz' P) (gen_pub_aexp sz' P)));
             (sz, thunkGen (fun _ => liftM2 AMult (gen_pub_aexp sz' P) (gen_pub_aexp sz' P)))]
  end.

Definition gen_secure_asgn (P:pub_vars) : G com :=
  let vars := map_dom (snd P) in
  x <- elems_ "X0"%string vars;;
  e <- (if apply P x then gen_pub_aexp 1 P else arbitrarySized 1);;
  ret <{ x := e }>.

Definition gen_name (P:pub_vars) (label:bool) : G (option string) :=
  let names := filter (fun x => Bool.eqb label (apply P x))
                      (map_dom (snd P)) in
  match names with
  | x0 :: _ => liftM Some (elems_ x0 names)
  | [] => ret None
  end.

Definition gen_asgn_in_ctx (gen_asgn : pub_vars -> G com)
    (pc:label) (P:pub_vars) : G com :=
  if pc then gen_asgn P
  else
    x <- gen_name P secret;; (* secret var *)
    match x with
    | Some x =>
      e <- arbitrarySized 1;;
      ret <{ x := e }>
    | None => ret <{ skip }>
    end.

Definition gen_secure_aread (P:pub_vars) (PA:pub_arrs) : G com :=
  let vars := map_dom (snd P) in
  x <- elems_ "X0"%string vars;;
  if apply P x then
    a <- gen_name PA public;; (* public array *)
    match a with
    | Some a =>
        i <- gen_pub_aexp 1 P;; (* public index *)
        ret <{ x <- a[[i]] }>
    | None => ret <{ skip }>
    end
  else
    a <- arbitrary;;
    i <- arbitrarySized 1;;
    ret <{ x <- a[[i]] }>.

Definition gen_aread_in_ctx (gen_aread : pub_vars -> pub_arrs -> G com)
    (pc:label) (P:pub_vars) (PA:pub_arrs) : G com :=
  if pc then gen_aread P PA
  else
    x <- gen_name P secret;; (* secret var *)
    match x with
    | Some x =>
      a <- arbitrary;;
      i <- arbitrarySized 1;;
      ret <{ x <- a[[i]] }>
    | None => ret <{ skip }>
    end.

Definition gen_secure_awrite (P:pub_vars) (PA:pub_arrs) : G com :=
  let arrs := map_dom (snd PA) in
  a <- elems_ "A0"%string arrs;;
  if apply PA a then
    i <- gen_pub_aexp 1 P;; (* public index *)
    e <- gen_pub_aexp 1 P;; (* public expression *)
    ret <{ a[i] <- e }>
  else
    i <- arbitrarySized 1;;
    e <- arbitrarySized 1;;
    ret <{ a[i] <- e }>.

Definition gen_awrite_in_ctx (gen_awrite : pub_vars -> pub_arrs -> G com)
    (pc:label) (P:pub_vars) (PA:pub_arrs) : G com :=
  if pc then gen_awrite P PA
  else
    a <- gen_name PA secret;; (* secret array *)
    match a with
    | Some a =>
      i <- arbitrarySized 1;;
      e <- arbitrarySized 1;;
      ret <{ a[i] <- e }>
    | None => ret <{ skip }>
    end.

Fixpoint gen_com_rec (gen_asgn : pub_vars -> G com)
                     (gen_aread : pub_vars -> pub_arrs -> G com)
                     (gen_awrite : pub_vars -> pub_arrs -> G com)
                     (P:pub_vars) (PA:pub_arrs) (sz:nat) : G com :=
  match sz with
  | O => freq [(1, ret Skip);
               (4, thunkGen (fun _ => gen_asgn P));
               (4, thunkGen (fun _ => gen_aread P PA));
               (4, thunkGen (fun _ => gen_awrite P PA))]
  | S sz' =>
      freq [ (1, ret Skip);
             (sz, thunkGen (fun _ => gen_asgn P));
             (sz, thunkGen (fun _ => gen_aread P PA));
             (sz, thunkGen (fun _ => gen_awrite P PA));
             (2*sz, thunkGen (fun _ =>
                    liftM2 Seq (gen_com_rec gen_asgn gen_aread gen_awrite P PA sz')
                               (gen_com_rec gen_asgn gen_aread gen_awrite P PA sz')));
             (sz, thunkGen (fun _ =>
                  b <- arbitrarySized 1;;
                  liftM3 If (ret b)
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b))
                                 (gen_aread_in_ctx gen_aread (label_of_bexp P b))
                                 (gen_awrite_in_ctx gen_awrite (label_of_bexp P b))
                                 P PA sz')
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b))
                                 (gen_aread_in_ctx gen_aread (label_of_bexp P b))
                                 (gen_awrite_in_ctx gen_awrite (label_of_bexp P b))
                                 P PA sz')));
             (sz, thunkGen (fun _ =>
                  b <- arbitrarySized 1;;
                  liftM2 While (ret b)
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b))
                                 (gen_aread_in_ctx gen_aread (label_of_bexp P b))
                                 (gen_awrite_in_ctx gen_aread (label_of_bexp P b))
                       P PA sz')))]
  end.

Definition gen_wt_com := gen_com_rec gen_secure_asgn gen_secure_aread gen_secure_awrite.

Sample gen_pub_vars.

Definition someP := (false, [("X0", false); ("X1", true); ("X2", true);
                             ("X3", true); ("X4", false); ("X5", false)])%string.

Sample gen_pub_arrs.

Definition somePA := (true, [("A0", true); ("A1", true); ("A2", false)])%string.

Sample (sized (gen_wt_com someP somePA)).

(* Strange that we need such a big hack here, but if we use AllPub we don't get
   public variables/arrays generated *)
Definition gen_com := gen_wt_com
                        (true, [("X0", true); ("X1", true); ("X2", true);
                          ("X3", true); ("X4", true); ("X5", true)])%string
                        (true, [("A0", true); ("A1", true); ("A2", true)])%string.

Sample (sized gen_com).

(* Preventing empty arrays *)
Definition gen_astate : G astate :=
  ld <- choose (1,10);;
  d <- vectorOf ld arbitrary;;
  l0 <- choose (1,10);;
  v0 <- vectorOf l0 arbitrary;;
  l1 <- choose (1,10);;
  v1 <- vectorOf l1 arbitrary;;
  l2 <- choose (1,10);;
  v2 <- vectorOf l2 arbitrary;;
  ret (d, [("A0",v0); ("A1",v1); ("A2",v2)]) % string.

(* Extract Constant defNumTests => "1000000". *)

(* We first validate that our generator produces well-typed terms *)

QuickChick (forAll gen_pub_vars (fun P =>
           (forAll gen_pub_arrs (fun PA =>
           (forAll (sized (gen_wt_com P PA)) (fun (c:com) =>
             wt_typechecker P PA public c)))))).

(* Noninterference for source sequential execution *)
QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>
    forAll (sized (gen_wt_com P PA)) (fun c =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    forAll gen_astate (fun a1 =>
    forAll (gen_pub_equiv_and_same_length PA a1) (fun a2 =>
      let r1 := cteval_engine 10 c s1 a1 in
      let r2 := cteval_engine 10 c s2 a2 in
      match (r1, r2) with
      | (Some (s1', a1', os1), Some (s2', a2', os2)) =>
          checker ((pub_equivb P s1' s2') && (pub_equivb_astate PA a1' a2'))
      | _ => checker tt (* discard *)
      end
  )))))))).

(* For testing relative security we do taint tracking of sequential executions
   (as a variant of Lucie's interpreter). We use this to track which initial
   values of variables and arrays affect CT observations. *)

Definition taint : Type := list (var_id + arr_id).

#[export] Instance showTaint : Show (var_id + arr_id) :=
  {show := fun x =>
     match x with
     | inl x => show x
     | inr a => show a
     end}.

Fixpoint remove_dupes {a:Type} (eqb:a->a->bool) (t : list a) : list a :=
  match t with
  | [] => []
  | x :: xs => if existsb (eqb x) xs
               then      remove_dupes eqb xs
               else x :: remove_dupes eqb xs
  end.

Definition sum_eqb (s1 s2 : (var_id + arr_id)) : bool :=
  match s1, s2 with
  | inl x1, inl x2
  | inr x1, inr x2 => String.eqb x1 x2
  | _, _ => false
  end.

Definition join_taints t1 t2 := remove_dupes sum_eqb (t1 ++ t2).

Module TaintTracking.

Definition tstate := total_map taint.
Definition tastate := total_map taint.

Definition input_st : Type := state * astate * tstate * tastate.
Inductive output_st (A : Type) : Type :=
  | ROutOfFuel : output_st A
  | ROutOfBounds : output_st A
  | ROk : A -> obs -> input_st -> output_st A.

(* An 'evaluator A'. This is the monad.
   It transforms an input state into an output state, returning an A. *)
Record evaluator (A : Type) : Type := mkEvaluator
  { evaluate : input_st -> output_st A }.
(* An interpreter is a special kind of evaluator *)
Definition interpreter: Type := evaluator unit.

(* Generic monad operators *)
#[export] Instance monadEvaluator: Monad evaluator :=
  { ret := fun A value => mkEvaluator A (fun (ist : input_st) => ROk A value [] ist);
    bind := fun A B e f =>
      mkEvaluator B (fun (ist : input_st) =>
        match evaluate A e ist with
        | ROk _ value os1 ist'  =>
            match evaluate B (f value) ist' with
            | ROk _ value os2 ist'' => ROk B value (os1 ++ os2) ist''
            | ret => ret
            end
        | ROutOfBounds _ => ROutOfBounds B
        | ROutOfFuel _ => ROutOfFuel B
        end
      )
   }.

(* specialized operators *)
Definition finish : interpreter := ret tt.

Definition get_var (name : string): evaluator nat :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _, _, _) := ist in
    evaluate _ (ret (apply st name)) ist
  ).
Definition get_arr (name : string): evaluator (list nat) :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(_, ast, _, _) := ist in
    evaluate _ (ret (apply ast name)) ist
  ).
Definition set_var (name : string) (value : nat) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, tst, tast) := ist in
    let new_st := (name !-> value ; st) in
    evaluate _ finish (new_st, ast, tst, tast)
  ).
Definition set_arr (name : string) (value : list nat) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, tst, tast) := ist in
    let new_ast := (name !-> value ; ast) in
    evaluate _ finish (st, new_ast, tst, tast)
  ).
Definition eval_aexp (a : aexp) : evaluator nat :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _, _, _) := ist in
    let v := aeval st a in
    evaluate _ (ret v) ist
  ).
Definition eval_bexp (b : bexp) : evaluator bool :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _, _, _) := ist in
    let v := beval st b in
    evaluate _ (ret v) ist
  ).
Definition raise_out_of_bounds {a:Type} : evaluator a :=
  mkEvaluator _ (fun _ =>
    ROutOfBounds _
  ).
Definition raise_out_of_fuel {a:Type} : evaluator a :=
  mkEvaluator _ (fun _ =>
    ROutOfFuel _
  ).
Definition observe (o : observation) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    ROk _ tt [o] ist
  ).

Definition get_taint_of_vars (xs:list string) : evaluator taint :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(_, _, tst, _) := ist in
    evaluate _ (ret (remove_dupes sum_eqb (List.concat (map (apply tst) xs)))) ist).

Definition get_taint_of_arr (a:string) : evaluator taint :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(_, _, _, tast) := ist in
    evaluate _ (ret (apply tast a)) ist).

Definition set_var_taint (x : string) (t : taint) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, tst, tast) := ist in
    let new_tst := (x !-> remove_dupes sum_eqb t ; tst) in
    evaluate _ finish (st, ast, new_tst, tast)).

Definition add_arr_taint (a : string) (t : taint) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, tst, tast) := ist in
    let new_tast := (a !-> (join_taints t (apply tast a)); tast) in
    evaluate _ finish (st, ast, tst, new_tast)).

Fixpoint taint_track (f : nat) (c : com) : evaluator taint :=
  match f with
  | O => raise_out_of_fuel
  | S f =>

  match c with
  | <{ skip }> =>
      ret []
  | <{ x := e }> =>
      v <- eval_aexp e;;
      set_var x v;;
      t <- get_taint_of_vars (vars_aexp e);;
      set_var_taint x t;;
      ret []
  | <{ c1 ; c2 }> =>
      t1 <- taint_track f c1;;
      t2 <- taint_track f c2;;
      ret (join_taints t1 t2)
  | <{ if b then ct else cf end }> =>
      condition <- eval_bexp b;;
      let next_c := if Bool.eqb condition true then ct else cf in
      observe (OBranch condition);;
      tb <- get_taint_of_vars (vars_bexp b);;
      t <- taint_track f next_c;;
      ret (join_taints tb t)
  | <{ while be do c end }> =>
    taint_track f <{
      if be then
        c;
        while be do c end
      else
        skip
      end
    }>
  | <{ x <- a[[ie]] }> =>
      i <- eval_aexp ie;;
      l <- get_arr a;;
      if (i <? List.length l) then
        observe (OARead a i);;
        set_var x (nth i l 0);;
        ti <- get_taint_of_vars (vars_aexp ie);;
        ta <- get_taint_of_arr a;;
        set_var_taint x (join_taints ti ta);;
        (ret ti)
      else
        raise_out_of_bounds
  | <{ a[ie] <- e }> =>
      n <- eval_aexp e;;
      i <- eval_aexp ie;;
      l <- get_arr a;;
      if (i <? List.length l) then
        observe (OAWrite a i);;
        set_arr a (upd i l n);;
        ti <- get_taint_of_vars (vars_aexp ie);;
        te <- get_taint_of_vars (vars_aexp e);;
        add_arr_taint a (join_taints ti te);;
        (ret ti)
      else
        raise_out_of_bounds
  end
  end.

End TaintTracking.

Fixpoint split_sum_list {A B : Type} (l : list (A + B)) : (list A * list B) :=
  match l with
  | [] => ([], [])
  | inl a :: xs => let (la, lb) := split_sum_list xs in (a :: la, lb)
  | inr b :: xs => let (la, lb) := split_sum_list xs in (la, b :: lb)
  end.

Definition taint_tracking (f : nat) (c : com) (st : state) (ast : astate)
    : option (state * astate * obs * list string * list string) :=
  let tst := ([], map (fun x => (x,[@inl var_id arr_id (Var x)])) (map_dom (snd st))) in
  let tast := ([], map (fun a => (a,[@inr var_id arr_id (Arr a)])) (map_dom (snd ast))) in
  let ist := (st, ast, tst, tast) in
  match TaintTracking.evaluate _ (TaintTracking.taint_track f c) ist with
  | TaintTracking.ROk _ t os (st', ast', _, _) =>
      let (vars, arrs) := split_sum_list t in
      Some (st', ast', os, remove_dupes String.eqb (map var_id_to_string vars),
                           remove_dupes String.eqb (map arr_id_to_string arrs))
  | _ => None
  end.

(* We first test the taint_tracking itself: it needs to enforce that if we make
   the initial values of the leaked variables/arrays public we can vary all the
   remaining secret variables/arrays and still obtain the same CT leakage. *)

QuickChick(
  forAll (sized gen_com) (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_astate (fun a1 =>
  let r1 := taint_tracking 10 c s1 a1 in
  match r1 with
  | Some (s1', a1', os1', tvars, tarrs) =>
      (* trace ("Leaked vars: " ++ show tvars ++ " arrs: " ++ show tarrs ++ nl) ( *)
      (* collect (show (List.length tvars + List.length tarrs)) ( *)
      let P := (false, map (fun x => (x,true)) tvars) in
      let PA := (false, map (fun a => (a,true)) tarrs) in
      forAll (gen_pub_equiv P s1) (fun s2 =>
      forAll (gen_pub_equiv_and_same_length PA a1) (fun a2 =>
      let r2 := cteval_engine 10 c s2 a2 in
      match r2 with
      | Some (s2', a2', os2') => checker (obs_eqb os1' os2')
      | None => checker tt (* discard *)
      end))
   | None => checker tt (* discard *)
   end)))).

(* Testing noninterference for target speculative execution *)

Definition extend_pub (P:pub_vars) (xs:list string) :=
  fold_left (fun P x => x !-> public; P) xs P.

Definition check_speculative_noninterference P PA c hardened : Checker :=
  forAll gen_state (fun s1 =>
  let s1 := ("b" !-> 0; s1) in
  forAll gen_astate (fun a1 =>
  let r1 := taint_tracking 10 c s1 a1 in
  match r1 with
  | Some (s1', a1', os1', tvars, tarrs) =>
      collect (show (List.length os1')) (
      (* collect (show (List.length (tvars ++ tarrs))) ( *)
      forAll (gen_pub_equiv (extend_pub P tvars) s1) (fun s2 =>
      let s2 := ("b" !-> 0; s2) in
      forAll (gen_pub_equiv_and_same_length (extend_pub PA tarrs) a1) (fun a2 =>
      let r2 := cteval_engine 10 c s2 a2 in
      match r2 with
      | Some (s2', a2', os2') =>
          (* implication (obs_eqb os1' os2') -- no longer needed *)
          (forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100)
             (fun '(ds, s1', a1', b', os1) =>
                match spec_eval_engine hardened s2 a2 false ds with
                | Some (s2', a2', b'', os2) =>
                    checker (Bool.eqb b' b'' && (pub_equivb P s1' s2') &&
                           (b' || (* <-- needed since we don't (yet) mask stores *)
                                  pub_equivb_astate PA a1' a2'))
                | None => checker tt (* discard -- doesn't seem to happen *)
                end))
      | None => checker tt (* discard -- doesn't seem to happen *)
      end)))
  | None => checker tt (* discard *)
  end)).

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  check_speculative_noninterference P PA c (flex_slh P c))))).

(* One may wonder if this property is enforced ENTIRELY by the source type
   system and would hold for any transformation that doesn't introduce (explicit
   or implicit) information flows, including no transformation at all?
   This doesn't work though because of out of bounds loads, and testing can
   find it -- SHOULD FAIL: *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  check_speculative_noninterference P PA c c)))).

(* In fact this doesn't even work for CT programs -- SHOULD FAIL: *)

Definition gen_ct_well_typed P PA := sized (gen_ct_well_typed_sized P PA).

QuickChick (
  forAllShrink gen_pub_vars shrink (fun P =>
  forAllShrink gen_pub_arrs shrink (fun PA =>
  forAllShrink (gen_ct_well_typed P PA) (shrink_ct_well_typed P PA) (fun c =>
  check_speculative_noninterference P PA c c)))).

(* This was the main reason for introducing sel_slh, which satisfies something
   even stronger as we proved in SpecCT.v (and we are testing it anyway below). *)

(* Testing flex_slh_relative_secure *)

Definition check_relative_security P PA c hardened : Checker :=
  forAll gen_state (fun s1 =>
  let s1 := ("b" !-> 0; s1) in
  forAll gen_astate (fun a1 =>
  let r1 := taint_tracking 10 c s1 a1 in
  match r1 with
  | Some (s1', a1', os1', tvars, tarrs) =>
      collect (show (List.length os1')) (
      (* collect (show (List.length (tvars ++ tarrs))) ( *)
      forAll (gen_pub_equiv (extend_pub P tvars) s1) (fun s2 =>
      let s2 := ("b" !-> 0; s2) in
      forAll (gen_pub_equiv_and_same_length (extend_pub PA tarrs) a1) (fun a2 =>
      let r2 := cteval_engine 10 c s2 a2 in
      match r2 with
      | Some (s2', a2', os2') =>
          (* implication (obs_eqb os1' os2') -- no longer needed *)
          (forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100)
             (fun '(ds, s1', a1', b', os1) =>
                match spec_eval_engine hardened s2 a2 false ds with
                | Some (s2', a2', b'', os2) => checker (obs_eqb os1 os2)
                | None => checker tt (* discard -- doesn't seem to happen *)
                end))
      | None => checker tt (* discard -- doesn't seem to happen *)
      end)))
  | None => checker tt (* discard *)
  end)).

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  check_relative_security P PA c (flex_slh P c))))).

(* Also testing Gilles' lemma here, not for ideal semantics, but for the translation *)

Definition check_gilles_lemma hardened s1 s2 : Checker :=
  let s1 := ("b" !-> 1; s1) in
  let s2 := ("b" !-> 1; s2) in
  forAll gen_astate (fun a1 =>
  forAll gen_astate (fun a2 => (* same length doesn't seem not needed *)
  forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100)
    (fun '(ds, s1', a1', b', os1) =>
       match spec_eval_engine hardened s2 a2 false ds with
       | Some (s2', a2', b'', os2) => checker (obs_eqb os1 os2)
       | None => checker tt (* discard *)
       end))).

(* Gilles' lemma as stated in UltimateSLH.v fails for flex_slh! -- SHOULD FAIL!
   Didn't expect it, but it makes sense in retrospect:
   for flex_slh public variables should *never* contain secrets,
   and our type-system ensures that *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_state (fun s2 =>
  check_gilles_lemma (flex_slh P c) s1 s2)))))).

(* A variant of Gilles' lemma works for flex_slh,
   but we need to only generate equivalent initial states *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 => (* <- extra assumption *)
  check_gilles_lemma (flex_slh P c) s1 s2)))))).

(* Directly testing also the top-level statement for OUR(!) Ultimate SLH,
   even if it is KIND OF(!) just a special case of flex_slh AllSecret. *)

Fixpoint our_ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ our_ultimate_slh c1; our_ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; our_ultimate_slh c1
                          else "b" := ("b" = 0 && be) ? 1 : "b"; our_ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; our_ultimate_slh c end;
         "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

Module RelatingOurUltimateSLH.
  (* our_ultimate_slh above is just a suboptimal version of `flex_slh AllSecret` *)

  (* Suboptimal because it even masks constant expressions, which clearly cannot
     leak secrets via observations. Still without such constant expressions we
     can prove it's the same. Here is a crude way of proving this using axioms
     that are generally false. *)

  Axiom no_constant_bexps : forall b, seq.nilp (vars_bexp b) = false.
  Axiom no_constant_aexps : forall a, seq.nilp (vars_aexp a) = false.

  Lemma our_ultimate_slh_is_flex_slh :
    forall c, our_ultimate_slh c = flex_slh AllSecret c.
  Proof.
    pose proof (fun b => all_secret_bexp b (no_constant_bexps b)).
    pose proof (fun b => all_secret_aexp b (no_constant_aexps b)).
    intros c. induction c; simpl; repeat rewrite_eq; reflexivity.
  Qed.

End RelatingOurUltimateSLH.

(* Testing our_ultimate_slh *)

(* Here is where taint_tracking really shines, since it halves the number of
   discards, and much more than that for long observations traces *)

QuickChick (
  forAll (sized gen_com) (fun c =>
  (check_relative_security AllSecret AllSecret c (our_ultimate_slh c)))).

QuickChick (
  forAll (sized gen_com) (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_state (fun s2 =>
  check_gilles_lemma (our_ultimate_slh c) s1 s2)))).

(* Finally, we check a very weak AllSecret instantiation of speculative
   noninterference, which only gives us something about the final flag. *)

QuickChick (
  forAll (sized gen_com) (fun c =>
  (check_speculative_noninterference AllSecret AllSecret c (our_ultimate_slh c)))).

(* This works without any protection though, probably because of the way our
   speculative semantics works and the fact that we share the directions. *)

QuickChick (
  forAll (sized gen_com) (fun c =>
  (check_speculative_noninterference AllSecret AllSecret c c))).

(* There is no other sound instantiation of P and PA that would satisfy the
   conclusion of check_speculative_noninterference for our_ultimate_slh and
   arbitrary programs though. Here is a very naive attempt -- SHOULD FAIL! *)

QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  forAllShrink gen_pub_vars shrink (fun P =>
  forAllShrink gen_pub_arrs shrink (fun PA =>
  (check_speculative_noninterference P PA c (our_ultimate_slh c)))))).

(* Now defining something closer to the original Ultimate SLH, even if it is
   just a special case of flex_slh AllSecret (we prove this below). *)

Fixpoint ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ ultimate_slh c1; ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      if seq.nilp (vars_bexp be) then (* optimized *)
        <{{if be then "b" := be ? "b" : 1; ultimate_slh c1
                 else "b" := be ? 1 : "b"; ultimate_slh c2 end}}>
      else
        <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c1
                            else "b" := ("b" = 0 && be) ? 1 : "b"; ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      if seq.nilp (vars_bexp be) then (* optimized *)
        <{{while be do "b" := be ? "b" : 1; ultimate_slh c end;
           "b" := be ? 1 : "b"}}>
      else
        <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c end;
           "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
      if seq.nilp (vars_aexp i) then (* optimized -- no mask even if it's out of bounds! *)
        <{{x <- a[[i]]}}>
      else
        <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> =>
      if seq.nilp (vars_aexp i) then (* optimized *)
        <{{a[i] <- e}}> (* <- Doing nothing here okay for Spectre v1,
         but problematic for return address or code pointer overwrites *)
      else
        <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

(* This original `ultimate_slh` is just `flex_slh AllSecret` *)

Lemma ultimate_slh_is_flex_slh :
  forall c, ultimate_slh c = flex_slh AllSecret c.
Proof.
  pose proof all_secret_bexp as Hb.
  pose proof all_secret_aexp as Ha.
  intros c. induction c; simpl; repeat rewrite_eq; try reflexivity.
  - destruct (seq.nilp (vars_bexp be)) eqn:Eq.
    + eapply no_vars_public_bexp in Eq. rewrite Eq. reflexivity.
    + erewrite Hb; eauto.
  - destruct (seq.nilp (vars_bexp be)) eqn:Eq.
    + eapply no_vars_public_bexp in Eq. rewrite Eq. reflexivity.
    + erewrite Hb; eauto.
  - destruct (seq.nilp (vars_aexp i)) eqn:Eq.
    + eapply no_vars_public_aexp in Eq. rewrite Eq. reflexivity.
    + erewrite Ha; eauto.
  - destruct (seq.nilp (vars_aexp i)) eqn:Eq.
    + eapply no_vars_public_aexp in Eq. rewrite Eq. reflexivity.
    + erewrite Ha; eauto.
Qed.

(* Testing ultimate_slh *)

QuickChick (
  forAll (sized gen_com) (fun c =>
  (check_relative_security AllSecret AllSecret c (ultimate_slh c)))).

QuickChick (
  forAll (sized gen_com) (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_state (fun s2 =>
  check_gilles_lemma (ultimate_slh c) s1 s2)))).

(** Now testing Standard SLH and Sel SLH *)

(** Standard SLH -- INSECURE FOR ARBITRARY PROGRAMS! SHOULD FAIL! *)

Definition slh := sel_slh AllPub.

QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  check_relative_security AllSecret AllSecret c (slh c))).

(* Standard SLH is secure for constant-time programs though *)
QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c =>
  check_relative_security P PA c (slh c))))).

(* But then for constant-time programs we should better use sel_slh *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c =>
  check_relative_security P PA c (sel_slh P c))))).

(* Also testing Gilles' lemma -- WRONG FOR ARBITRARY PROGRAMS! SHOULD FAIL! *)
QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  forAllShrink gen_state shrink (fun s1 =>
  forAllShrink gen_state shrink (fun s2 =>
  check_gilles_lemma (slh c) s1 s2)))).

(* This works for constant-time programs on equivalent initial states though *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c => (* <- extra assumption *)
  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 => (* <- extra assumption *)
  check_gilles_lemma (slh c) s1 s2)))))).

(* For constant-time programs we can use sel_slh though *)
QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c => (* <- extra assumption *)
  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 => (* <- extra assumption *)
  check_gilles_lemma (sel_slh P c) s1 s2)))))).

(* Finally, we can also check speculative noninterference for constant-time
   programs, but then for sel_slh we already proved a stronger version, which
   doesn't assume agreement of source leakages, so this is not a surprise. *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c =>
  check_speculative_noninterference P PA c (sel_slh P c))))).

(* Much more interestingly, I was expecting this to hold even for our weaker
   typing notion. But QuickChick found the beautiful counterexample below
   involving a loop that branches on an unmasked secret variable that gets
   assigned in the loop body and makes the directions go out of sync in the two
   executions, so the following public if gets different directions and based on
   that assigns or not to a public variable. So a new kind of implicit flow
   coming from running with different directions. SHOULD FAIL! *)

(* Since this is not consistently found with 10000 tests and shrinking doesn't
   work perfectly consistently even with forAllShrinkNonDet I've hard-coded the
   counterexample for now. Otherwise just set a larger number of tests and
   comment out the forAllShrinkNonDets: *)

(* Extract Constant defNumTests => "100000". *)

Definition forAllShrinkNonDet {A prop : Type} {_ : Checkable prop} `{Show A}
           (n : nat) (gen : G A) (shrinker : A -> list A) (pf : A -> prop) : Checker :=
  let repeated_shrinker (x : A) : list A :=
    List.concat (List.repeat (shrinker x) n) in
  bindGen gen (fun x : A =>
                 shrinking repeated_shrinker x (fun x' =>
                                         printTestCase (show x' ++ newline) (pf x'))).

Definition X0 := "X0"%string.
Definition X2 := "X2"%string.
Definition A0 := "A0"%string.
QuickChick (
  (* forAllShrinkNonDet 100 gen_pub_vars shrink (fun P => *)
  (* forAllShrinkNonDet 100 gen_pub_arrs shrink (fun PA => *)
  (* forAllShrinkNonDet 100 (sized (gen_wt_com P PA)) shrink (fun c => *)
  let P := (true, [("X0", true); ("X1", true); ("X2", false); ("X3", false); ("X4", false); ("X5", false)])%string in
  let PA := (true, [("A0", false); ("A1", true); ("A2", true)])%string in
  let c := <{{while (1 > X2) do (X2 <- A0[[0]]) end ; if (X0 > 0) then X0 := 0 else skip end}}> in
  implication (wt_typechecker P PA public c)
  (check_speculative_noninterference P PA c (sel_slh P c))).

(* Counterexamples also exist without while loops, but they are harder to find: *)
(* <{{if (0 <= 0) then (X0 := X0) else (if (1 > X3) then skip else (X0 <- A0[[X0]]) end) end}}> *)

(** * Exorcising Spectre SLH -- INSECURE! SHOULD FAIL! *)

Fixpoint exorcised_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ exorcised_slh c1; exorcised_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; exorcised_slh c1
                          else "b" := ("b" = 0 && be) ? 1 : "b"; exorcised_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; exorcised_slh c end;
         "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> => (* only masking output, this is wrong! *)
      <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  check_relative_security AllSecret AllSecret c (exorcised_slh c))).

(* Also testing Gilles' lemma -- SHOULD FAIL! *)
QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_state (fun s2 =>
  check_gilles_lemma (exorcised_slh c) s1 s2)))).
