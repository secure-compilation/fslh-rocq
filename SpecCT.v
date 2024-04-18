(** * SpecCT: Speculative Constant-Time *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(** * Cryptographic constant-time *)

(** Cryptographic constant-time (CCT) is a software countermeasure
    against cache-based timing attacks, a class of side-channel
    attacks that exploit the latency between cache hits and cache
    misses to retrieve cryptographic keys and other secrets. In
    addition to ensuring program counter security, CCT requires
    programmers to not perform memory accesses depending on secrets.

    To model this we first extend the Imp language with arrays. We
    need such an extension, since otherwise variable accesses in the
    original Imp map to memory operations at constant locations, which
    thus cannot depend on secrets, so CCT trivially holds for all
    programs in Imp. Array indices on the other hand are computed at
    runtime, which leads to accessing memory addresses that can depend
    on secrets, making CCT non-trivial for Imp with arrays. *)

(** ** Constant-time conditional *)

(** But first, we extend the arithmetic expressions of Imp with an [b ? e1 : e2]
    conditional that executes in constant time (for instance using a special
    constant-time conditional move instruction). This constant-time conditional
    makes arithmetic and boolean expressions mutually inductive. *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ACTIf (b:bexp) (a1 a2:aexp) (* <--- NEW *)
with bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Scheme aexp_bexp_ind := Induction for aexp Sort Prop
with bexp_aexp_ind := Induction for bexp Sort Prop.
Combined Scheme aexp_bexp_mutind from aexp_bexp_ind,bexp_aexp_ind.

(** ** Typing Constant-time conditional *)

(** Typing of arithmetic and boolean expressions also becomes mutually inductive. *)

(** [[[
        P|-b- be \in l   P |-a- a1 \in l1    P |-a- a2 \in l2
        ----------------------------------------------------- (T_CTIf)
                 P |-a- be?a1:a2 \in join l (join l1 l2)
]]]
*)

(* TERSE: HIDEFROMHTML *)
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "be '?' a1 ':' a2"  := (ACTIf be a1 a2)
                 (in custom com at level 20, no associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.
(* TERSE: /HIDEFROMHTML *)

(** ** Now back to adding arrays *)

Inductive com : Type :=
  | Skip
  | Asgn (x : string) (e : aexp)
  | Seq (c1 c2 : com)
  | If (be : bexp) (c1 c2 : com)
  | While (be : bexp) (c : com)
  | ARead (x : string) (a : string) (i : aexp) (* <--- NEW *)
  | AWrite (a : string) (i : aexp) (e : aexp)  (* <--- NEW *).

(* HIDE: CH: Wanted to take a:aexp and compute the accessed array, but
   our maps only have string keys, so had to settle with a:string for
   now. Seems this still fine though. *)

(* HIDE: CH: One alternative (also pointed out by Sven Argo) is that if
   we generalize/duplicate our map library beyond strings we can just
   make memory a single big array of numbers indexed by dynamically
   computed numbers. This would be a lower-level variant of Imp and
   one advantage over the variant with arrays is that our state would
   be a single map, not two. One advantage of the array variant is
   that we can use our existing variables as registers that can be
   accessed without triggering observable events, so our
   noninterference for expressions doesn't change, which is good.  *)

(* HIDE: CH: Maybe a good way to get the best of both worlds would
   be to use a type system to combine the two states into one, yet to
   keep accessing the arrays only with the special ARead and AWrite
   operations above. This would make this part of the chapter depend
   on types, while currently we manged to avoid that dependency, at
   the cost of duplicating the state. If avoiding the dependency is
   important we could dynamically prevent nat vs array type confusion
   for now and only return later to prevent it using static typing? *)

(* TERSE: HIDEFROMHTML *)

Notation "<{{ e }}>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.

Notation "'skip'"  :=
  Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (Asgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (in custom com at level 89, x custom com at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (While x y)
    (in custom com at level 89, x custom com at level 99, y at level 99) : com_scope.

(* HIDE *)
Check <{{ skip }}>.
Check <{{ (skip ; skip) ; skip }}>.
Check <{ 1 + 2 }>.
Check <{ 2 = 1 }>.
Check <{{ Z := X }}>.
Check <{{ Z := X + 3 }}>.
Definition func (c : com) : com := <{{ c ; skip }}>.
Check <{{ skip; func <{{ skip }}> }}>.
Definition func2 (c1 c2 : com) : com := <{{ c1 ; c2 }}>.
Check <{{ skip ; func2 <{{skip}}> <{{skip}}> }}>.
Check <{ true && ~(false && true) }>.
Check <{{ if true then skip else skip end }}>.
Check <{{ if true && true then skip; skip else skip; X:=X+1 end }}>.
Check <{{ while Z <> 0 do Y := Y * Z; Z := Z - 1 end }}>.
(* /HIDE *)

Notation "x '<-' a '[[' i ']]'"  :=
  (ARead x a i)
     (in custom com at level 0, x constr at level 0,
      a at level 85, i custom com at level 85, no associativity) : com_scope.
Notation "a '[' i ']'  '<-' e"  :=
  (AWrite a i e)
     (in custom com at level 0, a constr at level 0,
      i custom com at level 0, e custom com at level 85,
         no associativity) : com_scope.

Definition state := total_map nat.
Definition astate := total_map (list nat).

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | <{b ? a1 : a2}> => if beval st b then aeval st a1
          (* ^- NEW -> *)            else aeval st a2
  end
with beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

Fixpoint upd (i:nat) (ns:list nat) (n:nat) : list nat :=
  match i, ns with
  | 0, _ :: ns' => n :: ns'
  | S i', _ :: ns' => upd i' ns' n
  | _, _ => ns
  end.
(* TERSE: /HIDEFROMHTML *)

(** ** Observations *)

Inductive observation : Type :=
  | OBranch (b : bool)
  | OARead (a : string) (i : nat)
  | OAWrite (a : string) (i : nat).

Definition obs := list observation.

(** We define an instrumented big-step operational semantics based on these
   observations. *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation
         "'<(' st , ast ')>' '=[' c ']=>' '<(' stt , astt , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive cteval : com -> state -> astate -> state -> astate -> obs -> Prop :=
  | CTE_Skip : forall st ast,
      <(st , ast)> =[ skip ]=> <(st, ast, [])>
  | CTE_Asgn  : forall st ast e n x,
      aeval st e = n ->
      <(st, ast)> =[ x := e ]=> <(x !-> n; st, ast, [])>
  | CTE_Seq : forall c1 c2 st ast st' ast' st'' ast'' os1 os2,
      <(st, ast)> =[ c1 ]=> <(st', ast', os1)>  ->
      <(st', ast')> =[ c2 ]=> <(st'', ast'', os2)> ->
      <(st, ast)>  =[ c1 ; c2 ]=> <(st'', ast'', os1++os2)>
  | CTE_IfTrue : forall st ast st' ast' b c1 c2 os1,
      beval st b = true ->
      <(st, ast)> =[ c1 ]=> <(st', ast', os1)> ->
      <(st, ast)> =[ if b then c1 else c2 end]=> <(st', ast', OBranch true::os1)>
  | CTE_IfFalse : forall st ast st' ast' b c1 c2 os1,
      beval st b = false ->
      <(st, ast)> =[ c2 ]=> <(st', ast', os1)> ->
      <(st, ast)> =[ if b then c1 else c2 end]=> <(st', ast', OBranch false::os1)>
  | CTE_While : forall b st ast st' ast' os c,
      <(st,ast)> =[ if b then c; while b do c end else skip end ]=>
        <(st', ast', os)> -> (* <^- Nice trick; from small-step semantics *)
      <(st,ast)> =[ while b do c end ]=> <(st', ast', os)>
  | CTE_ARead : forall st ast x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      <(st, ast)> =[ x <- a[[ie]] ]=> <(x !-> nth i (ast a) 0; st, ast, [OARead a i])>
  | CTE_Write : forall st ast a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      <(st, ast)> =[ a[ie] <- e ]=> <(st, a !-> upd i (ast a) n; ast, [OAWrite a i])>

  where "<( st , ast )> =[ c ]=> <( stt , astt , os )>" := (cteval c st ast stt astt os).
(* TERSE: /HIDEFROMHTML *)

(** ** Type system for cryptographic constant-time programming *)

(* TERSE: HIDEFROMHTML *)
Definition label := bool.

Definition public : label := true.
Definition secret : label := false.

Definition pub_vars := total_map label.

Definition pub_equiv (P : pub_vars) {X:Type} (s1 s2 : total_map X) :=
  forall x:string, P x = true -> s1 x = s2 x.

Lemma pub_equiv_refl : forall {X:Type} (P : pub_vars) (s : total_map X),
  pub_equiv P s s.
Proof. intros X P s x Hx. reflexivity. Qed.

Lemma pub_equiv_sym : forall {X:Type} (P : pub_vars) (s1 s2 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s1.
Proof. unfold pub_equiv. intros X P s1 s2 H x Px. rewrite H; auto. Qed.

Lemma pub_equiv_trans : forall {X:Type} (P : pub_vars) (s1 s2 s3 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s3 ->
  pub_equiv P s1 s3.
Proof. unfold pub_equiv. intros X P s1 s2 s3 H12 H23 x Px.
       rewrite H12; try rewrite H23; auto. Qed.

Definition join (l1 l2 : label) : label := l1 && l2.

Lemma join_public : forall {l1 l2},
  join l1 l2 = public -> l1 = public /\ l2 = public.
Proof. apply andb_prop. Qed.

Definition can_flow (l1 l2 : label) : bool := l1 || negb l2.

Reserved Notation "P '|-a-' a \in l" (at level 40).
Reserved Notation "P '|-b-' b \in l" (at level 40).

Inductive aexp_has_label (P:pub_vars) : aexp -> label -> Prop :=
  | T_Num : forall n,
       P |-a- (ANum n) \in public
  | T_Id : forall X,
       P |-a- (AId X) \in (P X)
  | T_Plus : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ a1 + a2 }> \in (join l1 l2)
  | T_Minus : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ a1 - a2 }> \in (join l1 l2)
  | T_Mult : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ a1 * a2 }> \in (join l1 l2)
  | T_CTIf : forall be l a1 l1 a2 l2,
       P |-b- be \in l ->
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ be ? a1 : a2 }> \in (join l (join l1 l2))

where "P '|-a-' a '\in' l" := (aexp_has_label P a l)

with bexp_has_label (P:pub_vars) : bexp -> label -> Prop :=
  | T_True :
       P |-b- <{ true }> \in public
  | T_False :
       P |-b- <{ false }> \in public
  | T_Eq : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 = a2 }> \in (join l1 l2)
  | T_Neq : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 <> a2 }> \in (join l1 l2)
  | T_Le : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 <= a2 }> \in (join l1 l2)
  | T_Gt : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 > a2 }> \in (join l1 l2)
  | T_Not : forall b l,
       P |-b- b \in l ->
       P |-b- <{ ~b }> \in l
  | T_And : forall b1 l1 b2 l2,
       P |-b- b1 \in l1 ->
       P |-b- b2 \in l2 ->
       P |-b- <{ b1 && b2 }> \in (join l1 l2)

where "P '|-b-' b '\in' l" := (bexp_has_label P b l).

Scheme aexp_bexp_has_label_ind := Induction for aexp_has_label Sort Prop
with bexp_aexp_has_label_ind := Induction for bexp_has_label Sort Prop.
Combined Scheme aexp_bexp_has_label_mutind
  from aexp_bexp_has_label_ind,bexp_aexp_has_label_ind.

Theorem noninterferent_aexp_bexp : forall P s1 s2,
  pub_equiv P s1 s2 ->
  (forall a l, P |-a- a \in l ->
   l = public -> aeval s1 a = aeval s2 a) /\
  (forall b l, P |-b- b \in l ->
   l = public -> beval s1 b = beval s2 b).
Proof.
  intros P s1 s2 Heq. apply (aexp_bexp_has_label_mutind P);
    simpl; intros;
    (repeat match goal with
    | [Heql : join _ _ = public |- _] =>
      let G1 := fresh "G1" in
      let G2 := fresh "G2" in
      destruct (join_public Heql) as [G1 G2];
      rewrite G1 in *; rewrite G2 in *
    end); try reflexivity; eauto; firstorder;
    (repeat match goal with
    | [IH : aeval s1 ?a = aeval s2 ?a |- _] => rewrite IH
    end);
    (repeat match goal with
    | [IH : beval s1 ?b = beval s2 ?b |- _] => rewrite IH
    end); reflexivity.
Qed.

Theorem noninterferent_aexp : forall {P s1 s2 a},
  pub_equiv P s1 s2 ->
  P |-a- a \in public ->
  aeval s1 a = aeval s2 a.
Proof.
  intros P s1 s2 a Heq Ht. remember public as l.
  generalize dependent Heql. generalize dependent l.
  apply noninterferent_aexp_bexp. assumption.
Qed.

Theorem noninterferent_bexp : forall {P s1 s2 b},
  pub_equiv P s1 s2 ->
  P |-b- b \in public ->
  beval s1 b = beval s2 b.
Proof.
  intros P s1 s2 b Heq Ht. remember public as l.
  generalize dependent Heql. generalize dependent l.
  apply noninterferent_aexp_bexp. assumption.
Qed.

(* TERSE: /HIDEFROMHTML *)

Definition pub_arrs := total_map label.

(** [[[
                         ------------------                 (CT_Skip)
                         P ;; PA |-ct- skip

             P |-a- a \in l    can_flow l (P X) = true
             -----------------------------------------      (CT_Asgn)
                       P ;; PA |-ct- X := a

               P ;; PA |-ct- c1    P ;; PA |-ct- c2
               ------------------------------------          (CT_Seq)
                       P ;; PA |-ct- c1;c2

  P |-b- b \in public    P ;; PA |-ct- c1    P ;; PA |-ct- c2
  ----------------------------------------------------------- (CT_If)
               P ;; PA |-ct- if b then c1 else c2

                  P |-b- b \in public    P |-ct- c
                  --------------------------------         (CT_While)
                  P ;; PA |-ct- while b then c end

      P |-a- i \in public   can_flow (PA a) (P x) = true
      --------------------------------------------------   (CT_ARead)
                  P ;; PA |-ct- x <- a[[i]]

P |-a- i \in public   P |-a- e \in l   can_flow l (PA a) = true
--------------------------------------------------------------- (CT_AWrite)
                   P ;; PA |-ct- a[i] <- e
]]]
*)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "P ';;' PA '|-ct-' c" (at level 40).

Inductive ct_well_typed (P:pub_vars) (PA:pub_arrs) : com -> Prop :=
  | CT_Skip :
      P ;; PA |-ct- <{{ skip }}>
  | CT_Asgn : forall X a l,
      P |-a- a \in l ->
      can_flow l (P X) = true ->
      P ;; PA |-ct- <{{ X := a }}>
  | CT_Seq : forall c1 c2,
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- c2 ->
      P ;; PA |-ct- <{{ c1 ; c2 }}>
  | CT_If : forall b c1 c2,
      P |-b- b \in public ->
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- c2 ->
      P ;; PA |-ct- <{{ if b then c1 else c2 end }}>
  | CT_While : forall b c1,
      P |-b- b \in public ->
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- <{{ while b do c1 end }}>
  | CT_ARead : forall x a i,
      P |-a- i \in public ->
      can_flow (PA a) (P x) = true ->
      P ;; PA |-ct- <{{ x <- a[[i]] }}>
  | CT_AWrite : forall a i e l,
      P |-a- i \in public ->
      P |-a- e \in l ->
      can_flow l (PA a) = true ->
      P ;; PA |-ct- <{{ a[i] <- e }}>

where "P ;; PA '|-ct-' c" := (ct_well_typed P PA c).
(* TERSE: /HIDEFROMHTML *)

(** ** Final theorems: noninterference and constant-time security *)

Theorem ct_well_typed_noninterferent :
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2,
    P ;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    <(s1, a1)> =[ c ]=> <(s1', a1', os1)> ->
    <(s2, a2)> =[ c ]=> <(s2', a2', os2)> ->
    pub_equiv P s1' s2' /\ pub_equiv PA a1' a2'.
(* FOLD *)
Proof.
  intros P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent a2'. generalize dependent a2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - split; auto.
  - split; auto.
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      eapply noninterferent_aexp; eauto.
      subst. rewrite Hy in H11.
      unfold can_flow in H11. simpl in H11.
      destruct l; try discriminate. auto.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - edestruct IHHeval1_2; eauto.
    + eapply IHHeval1_1; eauto.
    + eapply IHHeval1_1; eauto.
  - eapply IHHeval1; eauto.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - eapply IHHeval1; eassumption.
  - eapply IHHeval1; eauto. repeat constructor; eassumption.
  - (* NEW CASE: ARead *)
    split; eauto.
    erewrite noninterferent_aexp; eauto.
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      subst. rewrite Hy in *.
      rewrite Haeq; eauto. now destruct (PA a).
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - (* NEW CASE: AWrite *)
    split; eauto.
    erewrite noninterferent_aexp; eauto.
    intros y Hy.
    destruct (String.eqb_spec a y) as [Hay | Hay].
    + rewrite Hay. do 2 rewrite t_update_eq.
      subst. rewrite Hy in *.
      rewrite Haeq; eauto.
      erewrite (noninterferent_aexp Heq); eauto. now destruct l.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hay).
      apply Haeq. apply Hy.
Qed.
(* /FOLD *)

Theorem ct_well_typed_ct_secure :
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2,
    P ;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    <(s1, a1)> =[ c ]=> <(s1', a1', os1)> ->
    <(s2, a2)> =[ c ]=> <(s2', a2', os2)> ->
    os1 = os2.
(* FOLD *)
Proof.
  intros P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent a2'. generalize dependent a2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
    + eapply ct_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption | eassumption ];
        eassumption.
    + eapply ct_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption | eassumption ];
        eassumption.
  - f_equal. eapply IHHeval1; try eassumption.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - f_equal. eapply IHHeval1; eassumption.
  - eapply IHHeval1; eauto. repeat constructor; eassumption.
  - (* NEW CASE: ARead *)
    f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* NEW CASE: AWrite *)
    f_equal. f_equal. eapply noninterferent_aexp; eassumption.
Qed.
(* /FOLD *)

(** * Speculative constant-time *)

(** This part is based on the "Spectre Declassified" paper from IEEE SP 2023,
    just in simplified form. *)

(** The observations are the same as above, so we can just reuse them. *)

Print observation.

(** We additionally add adversary provided directions to our semantics, which
    control speculation behavior. *)

Inductive direction :=
| DStep
| DForce
| DLoad (a : string) (i : nat)
| DStore (a : string) (i : nat).

Definition dirs := list direction.

Reserved Notation
         "'<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive spec_eval : com -> state -> astate -> bool -> dirs ->
                             state -> astate -> bool -> obs -> Prop :=
  | Spec_Skip : forall st ast b,
      <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Spec_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Spec_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os1++os2)>
  | Spec_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      <(st, ast, b, ds)> =[ match beval st be with
                       | true => c1
                       | false => c2 end ]=> <(st', ast', b', os1)> ->
      <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', OBranch (beval st be)::os1)>
  | Spec_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      <(st, ast, true, ds)> =[ match beval st be with
                       | true => c2 (* <-- branches swapped *)
                       | false => c1 end ]=> <(st', ast', b', os1)> ->
      <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', OBranch (beval st be)::os1)>
  | Spec_While : forall be st ast b ds st' ast' b' os c,
      <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Spec_ARead : forall st ast x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      <(st, ast, false, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i (ast a) 0; st, ast, false, [OARead a i])>
  | Spec_ARead_U : forall st ast x a ie i a' i',
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <(st, ast, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i' (ast a') 0; st, ast, true, [OARead a i])>
  | Spec_Write : forall st ast b a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (ast a) n; ast, b, [OAWrite a i])>
  | Spec_Write_U : forall st ast a ie i e n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <(st, ast, true, [DStore a' i'])> =[ a[ie] <- e ]=>
        <(st, a' !-> upd i' (ast a') n; ast, true, [OAWrite a i])>

  where "<( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (spec_eval c st ast b ds stt astt bb os).

(* HIDE: This semantics already lost one property of Imp, which is only
   nonterminating executions don't produce a final state. Now if the input
   directions don't match what the program expects we also get stuck, which for
   our big-step semantics can't be distinguished from nontermination. This is
   probably not a problem, but just wanted to mention it. *)

(** HIDE: Without fences the speculation bit [b] is just a form of instrumentation
    that doesn't affect the semantics, except adding more stuckness for the [_U] rules. *)

(* LATER: Could also add fences, but they are not needed for SLH. They would add
   a bit of complexity to the big-step semantics, since they behave like a halt
   instruction that prematurely ends execution, which means adding at least one
   more rule for sequencing (basically an error monad, but with a (halt) bit of
   cleverness we can probably avoid extra rules for if and while, since we're
   just threading through things). We likely don't want to treat this stuckness
   as not producing a final state though, since a stuck fence should be final
   state in their small-step semantics (actually they messed that up,
   see next point). *)

(* LATER: Could prove this semantics equivalent to the small-step one from the
   two IEEE SP 2023 papers. The fact that their rule [Seq-Skip] requires a step
   seems wrong if first command in the sequence is already skip. Also the way
   they define final results seem wrong for stuck fences, and that would either
   need to be fixed to include stuck fences deep inside or to bubble up stuck
   fences to the top (error monad, see prev point). *)

(* HIDE: Another fix I did to their semantics is in the (Spec_ARead) rule, which
   here requires no speculation, and in (Ideal_ARead_Prot) which takes the same
   direction as (Spec_Aread_U, not Spec_Aread). This reduces rule overlap, makes
   the Spec_ and Ideal_ semantics more aligned, and thus makes the SLH
   translation more correct. *)
(* SOONER: Restricting Spec_ARead to only apply for b = false seems funny in
   retrospect. *)

(* HIDE: One design decision here is to neither consume DSteps not to generate
   dummy observations for skip and (register) assignment commands. This leads to
   simpler proofs (e.g. no need for erasure) and it also seems sensible: it's
   not like a skip takes the same time as an assignment anyway, so making these
   things observable with the same dummy event seems anyway questionable! *)

(* LATER: Could add the declassify construct from Spectre Declassified, but for
   now trying to keep things simple. If we add that then the RNI notion of
   Definition 2 relies on the small-step semantics to stop at the first force
   directive. Doing that with a big-step semantics seems trickier. We could
   build a version that halts early on the first force? *)

(* SOONER: Give example programs that satisfy the cryptographic constant-time
   discipline ([ct_well_typed]), but that are insecure wrt the speculative
   semantics above.  For instance, one can write secrets to public arrays using
   Spec_Write_U, and one can read to public registers from secret Spec_ARead_U.
   Could look both into simple examples exploiting the semantics, and also into
   more realistic examples that one can also exploit in practice.

   b - secret array of size n >= 1
   a - public array of size n >= 1
   p - public variable

   Realistic example:
   i := 0;
   while i < n do
     p := p + a[i];
     i := i + 1;
   end

   Simple but not so realistic example
   (safe+secure without speculation, but unsafe+insecure with speculation):
   if false then p := a[n] else skip
*)

(* HIDE: Just to warm up formalized the first lemma in the Spectre Declassified
   paper: Lemma 1: structural properties of execution *)

Lemma speculation_bit_monotonic : forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = true ->
  b' = true.
Proof. intros c s a b ds s' a' b' os Heval Hb. induction Heval; eauto. Qed.

(* HIDE: This one is weaker for big-step semantics, but it's still helpful below *)
Lemma speculation_needs_force : forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = false ->
  b' = true ->
  In DForce ds.
Proof.
  intros c s a b ds s' a' b' os Heval Hb Hb'.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

(* HIDE: Also this one is weaker for big-step semantics *)
Lemma unsafe_access_needs_speculation : forall c s a b ds s' a' b' os ax i,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  In (DLoad ax i) ds \/ In (DStore ax i) ds ->
  b = true \/ In DForce ds.
Proof.
  intros c s a b ds s' a' b' os ax i Heval Hin.
  induction Heval; simpl in *; try tauto; try (firstorder; discriminate).
  - destruct Hin as [Hin | Hin].
    + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * specialize (IHHeval1 (or_introl _ Hin)). destruct IHHeval1; try tauto.
        right. apply in_or_app. tauto.
      * specialize (IHHeval2 (or_introl _ Hin)). destruct IHHeval2; try tauto.
        { destruct b eqn:Eq; try tauto.
          (* slightly more interesting case, the rest very boring *)
          right. apply speculation_needs_force in Heval1; [| reflexivity|assumption].
          apply in_or_app. tauto. }
        { right. apply in_or_app. tauto. }
    + (* very symmetric, mostly copy paste *)
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * specialize (IHHeval1 (or_intror _ Hin)). destruct IHHeval1; try tauto.
        right. apply in_or_app. tauto.
      * specialize (IHHeval2 (or_intror _ Hin)). destruct IHHeval2; try tauto.
        { destruct b eqn:Eq; try tauto.
          right. apply speculation_needs_force in Heval1; [| reflexivity|assumption].
          apply in_or_app. tauto. }
        { right. apply in_or_app. tauto. }
Qed.

(** We can recover sequential execution from [spec_eval] if there is no
    speculation, so all directives are [DStep] and speculation flag starts [false]. *)

Definition seq_spec_eval (c:com) (s:state) (a:astate)
    (s':state) (a':astate) (os:obs) : Prop :=
  exists ds, (forall d, In d ds -> d = DStep) /\
    <(s, a, false, ds)> =[ c ]=> <(s', a', false, os)>.

(* LATER: We should be able to prove that [cteval] and [seq_spec_eval] coincide, so
   by [ct_well_typed_ct_secure] also directly get their Lemma 2. *)

(** ** Speculative constant-time security definition *)

Definition spec_ct_secure :=
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' b1' b2' os1 os2 ds,
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    <(s1, a1, false, ds)> =[ c ]=> <(s1', a1', b1', os1)> ->
    <(s2, a2, false, ds)> =[ c ]=> <(s2', a2', b2', os2)> ->
    os1 = os2.

(** Selective SLH transformation that we will show enforces speculative
    constant-time security. *)

Fixpoint sel_slh (P:pub_vars) (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ sel_slh P c1; sel_slh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if be then "b" := (be ? "b" : 1); sel_slh P c1
               else "b" := (be ? 1 : "b"); sel_slh P c2 end}}>
  | <{{while be do c end}}> =>
      <{{while be do "b" := (be ? "b" : 1); sel_slh P c end;
         "b" := (be ? 1 : "b")}}>
  | <{{x <- a[[i]]}}> =>
      if P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
             else <{{x <- a[[i]]}}>
  | <{{a[i] <- e}}> => <{{a[i] <- e}}>
  end)%string.

(** To prove this transformation secure, Spectre Declassified uses an idealized semantics *)

Reserved Notation
         "P '|-' '<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval (P:pub_vars) :
    com -> state -> astate -> bool -> dirs ->
           state -> astate -> bool -> obs -> Prop :=
  | Ideal_Skip : forall st ast b,
      P |- <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Ideal_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      P |- <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Ideal_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      P |- <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      P |- <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      P |- <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os1++os2)>
  | Ideal_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      P |- <(st, ast, b, ds)> =[ match beval st be with
                                 | true => c1
                                 | false => c2 end ]=> <(st', ast', b', os1)> ->
      P |- <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', OBranch (beval st be)::os1)>
  | Ideal_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      P |- <(st, ast, true, ds)> =[ match beval st be with
                                    | true => c2 (* <-- branches swapped *)
                                    | false => c1 end ]=> <(st', ast', b', os1)> ->
      P |- <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', OBranch (beval st be)::os1)>
  | Ideal_While : forall be st ast b ds st' ast' b' os c,
      P |- <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      P |- <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Ideal_ARead : forall st ast x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      P |- <(st, ast, false, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i (ast a) 0; st, ast, false, [OARead a i])>
  | Ideal_ARead_U : forall st ast x a ie i a' i',
      P x = secret -> (* <-- NEW: this rule applies now only for loads into secret variables *)
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <(st, ast, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i' (ast a') 0; st, ast, true, [OARead a i])>
  | Ideal_ARead_Prot : forall st ast x a ie i a' i',
      P x = public ->  (* <-- NEW: new rule for loads into public variables *)
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <(st, ast, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> 0; st, ast, true, [OARead a i])>
  | Ideal_Write : forall st ast b a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      P |- <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (ast a) n; ast, b, [OAWrite a i])>
  | Ideal_Write_U : forall st ast a ie i e n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <(st, ast, true, [DStore a' i'])> =[ a[ie] <- e ]=>
        <(st, a' !-> upd i' (ast a') n; ast, true, [OAWrite a i])>

  where "P |- <( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (ideal_eval P c st ast b ds stt astt bb os).

(* We show that on sequential executions this is equivalent to [seq_spec_eval] *)

Lemma seq_eval_ideal_eval_ind1 : forall P c s a b ds s' a' b' os,
  (forall d : direction, In d ds -> d = DStep) ->
  <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )> ->
  b = false ->
  b' = false ->
  P |- <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )>.
Proof.
  intros P c s a b ds s' a' b' os Hds H Eb Eb'.
  induction H; try constructor; eauto.
  - assert(b' = false).
    { destruct b' eqn:Eqb'; [| reflexivity].
      apply speculation_needs_force in H; try tauto.
      assert (contra : DForce = DStep).
      { apply Hds. apply in_or_app. left. assumption. }
      inversion contra. }
    eapply Ideal_Seq.
    * apply IHspec_eval1; eauto using in_or_app.
    * apply IHspec_eval2; eauto using in_or_app.
  - simpl in Hds; eauto.
  - simpl in Hds.
    assert (contra : DForce = DStep). { apply Hds. left. reflexivity. }
    inversion contra.
  - discriminate.
Qed.

Lemma speculation_needs_force_ideal : forall P c s a b ds s' a' b' os,
  P |- <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = false ->
  b' = true ->
  In DForce ds.
Proof.
  intros P c s a b ds s' a' b' os Heval Hb Hb'.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

Lemma seq_eval_ideal_eval_ind2 : forall P c s a b ds s' a' b' os,
  (forall d : direction, In d ds -> d = DStep) ->
  P |- <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )> ->
  b = false ->
  b' = false ->
  <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )>.
Proof. (* proof really the same as gen1 *)
  intros P c s a b ds s' a' b' os Hds H Eb Eb'.
  induction H; try constructor; eauto.
  - assert(b' = false).
    { destruct b' eqn:Eqb'; [| reflexivity].
      apply speculation_needs_force_ideal in H; try tauto.
      assert (contra : DForce = DStep).
      { apply Hds. apply in_or_app. left. assumption. }
      inversion contra. }
    eapply Spec_Seq.
    * apply IHideal_eval1; eauto using in_or_app.
    * apply IHideal_eval2; eauto using in_or_app.
  - simpl in Hds; eauto.
  - simpl in Hds.
    assert (contra : DForce = DStep). { apply Hds. left. reflexivity. }
    inversion contra.
  - discriminate.
Qed.

(* HIDE: This is Lemma 3 from Spectre Declassified *)

Definition seq_ideal_eval (P:pub_vars) (c:com) (s:state) (a:astate)
    (s':state) (a':astate) (os:obs) : Prop :=
  exists ds, (forall d, In d ds -> d = DStep) /\
    P |- <(s, a, false, ds)> =[ c ]=> <(s', a', false, os)>.

Lemma seq_spec_eval_ideal_eval : forall P c s a s' a' os,
  seq_spec_eval c s a s' a' os <->
  seq_ideal_eval P c s a s' a' os.
Proof.
  intros P c s a s' a' os. unfold seq_spec_eval, seq_ideal_eval.
  split; intros [ds [Hds H] ]; exists ds; (split; [ apply Hds |]).
  - apply seq_eval_ideal_eval_ind1; eauto.
  - eapply seq_eval_ideal_eval_ind2; eauto.
Qed.

(** Let's now prove that the idealized semantics does enforce speculative constant-time *)

Definition prefix {X:Type} (xs ys : list X) : Prop :=
  exists zs, xs ++ zs = ys.

Lemma prefix_refl : forall {X:Type} {ds : list X},
  prefix ds ds.
Proof. intros X ds. exists []. apply app_nil_r. Qed.

Lemma prefix_nil : forall {X:Type} (ds : list X),
  prefix [] ds.
Proof. intros X ds. unfold prefix. eexists. simpl. reflexivity. Qed.

Lemma prefix_heads_and_tails : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2 /\ prefix t1 t2.
Proof.
  intros X h1 h2 t1 t2. unfold prefix. intros Hpre.
  destruct Hpre as [zs Hpre]; simpl in Hpre.
  inversion Hpre; subst. eauto.
Qed.

Lemma prefix_heads : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2.
Proof.
  intros X h1 h2 t1 t2 H. apply prefix_heads_and_tails in H; tauto.
Qed.

Lemma prefix_or_heads : forall {X:Type} (x y : X) (xs ys : list X),
  prefix (x :: xs) (y :: ys) \/ prefix (y :: ys) (x :: xs) ->
  x = y.
Proof.
  intros X x y xs ys H.
  destruct H as [H | H]; apply prefix_heads in H; congruence.
Qed.

Lemma prefix_cons : forall {X:Type} (d :X) (ds1 ds2: list X),
 prefix ds1 ds2 <->
 prefix (d::ds1) (d::ds2).
Proof.
  intros X d ds1 ds2. split; [unfold prefix| ]; intros H.
  - destruct H; subst.
    eexists; simpl; eauto.
  - apply prefix_heads_and_tails in H. destruct H as [_ H]. assumption.
Qed.

Lemma prefix_app : forall {X:Type} {ds1 ds2 ds0 ds3 : list X},
  prefix (ds1 ++ ds2) (ds0 ++ ds3) ->
  prefix ds1 ds0 \/ prefix ds0 ds1.
Proof. 
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds0 ds3 H.
  - left. apply prefix_nil.
  - destruct ds0 as [| d0 ds0'] eqn:D0.
    + right. apply prefix_nil.
    + simpl in H; apply prefix_heads_and_tails in H.
      destruct H as [Heq Hpre]; subst.
      apply IH in Hpre; destruct Hpre; [left | right];
      apply prefix_cons; assumption.
Qed.

Lemma prefix_append_front : forall {X:Type} {ds1 ds2 ds3 : list X},
  prefix (ds1 ++ ds2) (ds1 ++ ds3) ->
  prefix ds2 ds3.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds3 H.
  - auto.
  - simpl in H; apply prefix_cons in H. apply IH in H. assumption.
Qed.

Lemma app_eq_prefix : forall {X:Type} {ds1 ds2 ds1' ds2' : list X},
  ds1 ++ ds2 = ds1' ++ ds2' ->
  prefix ds1 ds1' \/ prefix ds1' ds1.
Proof. 
  intros X ds1. induction ds1 as [| h1 t1 IH]; intros ds2 ds1' ds2' H.
  - left. apply prefix_nil.
  - destruct ds1' as [| h1' t1'] eqn:D1'.
    + right. apply prefix_nil.
    + simpl in H; inversion H; subst.
      apply IH in H2. destruct H2 as [HL | HR];
      [left | right]; apply prefix_cons; auto.
Qed.

Ltac split4 := split; [|split; [| split] ].

Lemma ct_well_typed_ideal_noninterferent_general :
  forall P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds1 ds2,
    P ;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    (b = false -> pub_equiv PA a1 a2) ->
    (prefix ds1 ds2 \/ prefix ds2 ds1) -> (* <- interesting generalization *)
    P |- <(s1, a1, b, ds1)> =[ c ]=> <(s1', a1', b1', os1)> ->
    P |- <(s2, a2, b, ds2)> =[ c ]=> <(s2', a2', b2', os2)> ->
    pub_equiv P s1' s2' /\ b1' = b2' /\
      (b1' = false -> pub_equiv PA a1' a2') /\
      ds1 = ds2.  (* <- interesting generalization *)
Proof.
  intros P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds1 ds2
    Hwt Heq Haeq Hds Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent a2'. generalize dependent a2.
  generalize dependent os2. generalize dependent b2'.
  generalize dependent ds2.
  induction Heval1; intros ds2X Hds b2' os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - (* skip *) auto.
  - (* assign *) split4; auto.
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      eapply noninterferent_aexp; eauto.
      subst. rewrite Hy in H14.
      unfold can_flow in H14. simpl in H14.
      destruct l; try discriminate. auto.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - (* seq *) assert (Hds1: prefix ds1 ds0 \/ prefix ds0 ds1).
    { destruct Hds as [Hds | Hds]; apply prefix_app in Hds; tauto. }
    assert (ds1 = ds0). { eapply IHHeval1_1; eassumption. } subst.
    assert (Hds2: prefix ds2 ds3 \/ prefix ds3 ds2).
    { destruct Hds as [Hds | Hds]; apply prefix_append_front in Hds; tauto. }
    (* SOONER: proofs above and below can be better integrated *)
    specialize (IHHeval1_1 H13 _ Hds1 _ _ _ Haeq _ _ Heq _ H1).
    destruct IHHeval1_1 as [ IH12eq [IH12b [IH12eqa _] ] ]. subst.
    specialize (IHHeval1_2 H14 _ Hds2 _ _ _ IH12eqa _ _ IH12eq _ H10).
    firstorder; subst; reflexivity.
  - (* if (If) *)
    assert(G : P ;; PA |-ct- (if beval st be then c1 else c2)).
    { destruct (beval st be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    erewrite noninterferent_bexp in H10.
    + specialize (IHHeval1 G _ Gds _ _ _ Haeq _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* if contra *) apply prefix_or_heads in Hds; inversion Hds.
  - (* if contra *) apply prefix_or_heads in Hds; inversion Hds.
  - (* if (If_F) - very similar If *)
    assert(G : P ;; PA |-ct- (if beval st be then c2 else c1)).
    { destruct (beval st be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    erewrite noninterferent_bexp in H10.
    + assert(GG: true = false -> pub_equiv PA ast a2). (* <- only difference *)
      { intro Hc. discriminate. }
      specialize (IHHeval1 G _ Gds _ _ _ GG _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* while *) eapply IHHeval1; try eassumption. repeat constructor; eassumption.
  - (* array read (ARead) *) split4; eauto.
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      subst. rewrite Hy in *.
      rewrite Haeq; eauto.
      * erewrite noninterferent_aexp; eauto.
      * now destruct (PA a).
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - (* array read (ARead_U) *) split4; eauto.
    + intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
      * rewrite Hxy. do 2 rewrite t_update_eq.
        subst. rewrite Hy in *.
        rewrite Haeq; eauto.
        { apply prefix_or_heads in Hds. inversion Hds. reflexivity. }
        { now destruct (PA a). (* also discriminate works *) }
      * do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
        apply Heq. apply Hy.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
  - (* array read contra *) rewrite H in *. discriminate.
  - (* array read contra *) rewrite H in *. discriminate.
  - (* array read (ARead_Prot) *)
    assert(G : DLoad a' i' = DLoad a'0 i'0).
    { destruct Hds as [Hds | Hds]; inversion Hds; inversion H0; subst; reflexivity. }
    inversion G; subst. split4; eauto.
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq. reflexivity.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - (* array write (Write) *) split4; eauto. intro Hb2'.
    erewrite noninterferent_aexp; eauto.
    intros y Hy.
    destruct (String.eqb_spec a y) as [Hay | Hay].
    + rewrite Hay. do 2 rewrite t_update_eq.
      subst. rewrite Hy in *.
      rewrite Haeq; eauto.
      erewrite (noninterferent_aexp Heq); eauto. now destruct l.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hay).
      apply Haeq; assumption.
  - (* array write contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* array write contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* array write (Write_U) *) split4; eauto.
    + intro contra. discriminate contra.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
Qed.

(* SOONER: The cases for arrays above are repetitive. Spin off some lemmas. *)

Lemma ct_well_typed_ideal_noninterferent :
  forall P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds,
    P ;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    (b = false -> pub_equiv PA a1 a2) ->
    P |- <(s1, a1, b, ds)> =[ c ]=> <(s1', a1', b1', os1)> ->
    P |- <(s2, a2, b, ds)> =[ c ]=> <(s2', a2', b2', os2)> ->
    pub_equiv P s1' s2' /\ b1' = b2' /\ (b1' = false -> pub_equiv PA a1' a2').
Proof.
  intros P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  eapply ct_well_typed_ideal_noninterferent_general in Heval2; eauto; try tauto.
  left. apply prefix_refl.
Qed.

(** This corollary (used below) also follows from [noninterferent_general] *)
Corollary aux : forall P PA s1 s2 a1 a2 b ds1 ds2 c st1 st2 ast1 ast2 b1 b2 os1 os2 ds1' ds2',
  ds2 ++ ds2' = ds1 ++ ds1' ->
  P ;; PA |-ct- c ->
  pub_equiv P s1 s2 ->
  (b = false -> pub_equiv PA a1 a2) ->
  P |- <(s1, a1, b, ds1)> =[ c ]=> <(st1, ast1, b1, os1)>  ->
  P |- <(s2, a2, b, ds2)> =[ c ]=> <(st2, ast2, b2, os2)> ->
  ds1 = ds2 /\ ds1' = ds2'.
Proof.
  intros P PA s1 s2 a1 a2 b ds1 ds2 c st1 st2 ast1 ast2 b1 b2 os1 os2 ds1' ds2'
    Hds Hwt Heq Haeq Heval1 Heval2.
  pose proof Hds as H.
  symmetry in H.
  apply app_eq_prefix in H.
  eapply ct_well_typed_ideal_noninterferent_general in H;
    [ | | | | apply Heval1 | apply Heval2]; try eassumption.
  - destruct H as [ _ [ _ [ _ H] ] ]. subst. split; [reflexivity|].
    apply app_inv_head in Hds. congruence.
Qed.

Theorem ideal_spec_ct_secure :
  forall P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds,
    P ;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    (b = false -> pub_equiv PA a1 a2) ->
    P |- <(s1, a1, b, ds)> =[ c ]=> <(s1', a1', b1', os1)> ->
    P |- <(s2, a2, b, ds)> =[ c ]=> <(s2', a2', b2', os2)> ->
    os1 = os2.
Proof.
  intros P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent a2'. generalize dependent a2.
  generalize dependent os2. generalize dependent b2'.
  induction Heval1; intros b2' os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - (* seq *) eapply aux in H1; [| | | | apply Heval1_1 | apply H5 ]; eauto.
    destruct H1 as [H1 H1']. subst.
    assert(NI1 : pub_equiv P st' st'0 /\ b' = b'0 /\ (b' = false -> pub_equiv PA ast' ast'0)).
    { eapply ct_well_typed_ideal_noninterferent; [ | | | eassumption | eassumption]; eauto. }
    destruct NI1 as [NI1eq [NIb NIaeq] ]. subst.
    erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
  - f_equal.
    + f_equal. eapply noninterferent_bexp; eassumption.
    + eapply IHHeval1; try eassumption; try (destruct (beval st be); eassumption).
      erewrite noninterferent_bexp; eassumption.
  - f_equal.
    + f_equal. eapply noninterferent_bexp; eassumption.
    + eapply IHHeval1; try eassumption; try (destruct (beval st be); eassumption).
      * intro contra. discriminate contra.
      * erewrite noninterferent_bexp; eassumption.
  - eapply IHHeval1; eauto. repeat constructor; eassumption.
  - (* ARead *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* ARead_U/Prot *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* ARead_U/Prot *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* ARead_U/Prot *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* ARead_U/Prot *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* AWrite *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* AWrite *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
Qed.

(** We now prove that the idealized semantics is equivalent to [sel_slh]
    transformation (Lemma 6 and the more precise Lemma 7). *)

(** All results about [sel_slh] below assume that the original [c] doesn't
    already use the variable ["b"] needed by the [sel_slh] translation. *)

Fixpoint a_unused (x:string) (a:aexp) : Prop :=
  match a with
  | ANum n      => True
  | AId y       => y <> x
  | <{a1 + a2}>
  | <{a1 - a2}>
  | <{a1 * a2}> => a_unused x a1 /\ a_unused x a2
  | <{b ? a1 : a2}> => b_unused x b /\ a_unused x a1 /\ a_unused x a2
  end
with b_unused (x:string) (b:bexp) : Prop :=
  match b with
  | <{true}>
  | <{false}>     => True
  | <{a1 = a2}>
  | <{a1 <> a2}>
  | <{a1 <= a2}>
  | <{a1 > a2}>   => a_unused x a1 /\ a_unused x a2
  | <{~ b1}>      => b_unused x b1
  | <{b1 && b2}>  => b_unused x b1 /\ b_unused x b2
  end.

Fixpoint c_unused (x:string) (c:com) : Prop :=
  match c with
  | <{{skip}}> => True
  | <{{y := e}}> => y <> x /\ a_unused x e
  | <{{c1; c2}}> => c_unused x c1 /\ c_unused x c2
  | <{{if be then c1 else c2 end}}> =>
      b_unused x be /\ c_unused x c1 /\ c_unused x c2
  | <{{while be do c end}}> => b_unused x be /\ c_unused x c
  | <{{y <- a[[i]]}}> => y <> x /\ a_unused x i
  | <{{a[i] <- e}}> => a_unused x i /\ a_unused x e
  end.

Open Scope string_scope.

(** To simplify some proofs we also restrict to while-free programs for now. *)

(* SOONER: Even something as simple as [sel_slh_flag] below turns out to be hard
   for while loops, since it has the flavour of backwards compiler
   correctness. For backwards compiler correctness with while we probably need
   to use a small-step semantics and a simulation direction flipping trick? *)

Fixpoint c_no_while (c:com) : Prop :=
  match c with
  | <{{while _ do _ end}}> => False
  | <{{if _ then c1 else c2 end}}>
  | <{{c1; c2}}> => c_no_while c1 /\ c_no_while c2
  | _ => True
  end.

(** As a warm-up we prove that [sel_slh] properly updates the variable "b". *)

Lemma sel_slh_flag : forall c P s a (b:bool) ds s' a' (b':bool) os,
  c_unused "b" c ->
  c_no_while c ->
  s "b" = (if b then 1 else 0) ->
  <(s, a, b, ds)> =[ sel_slh P c ]=> <(s', a', b', os)> ->
  s' "b" = (if b' then 1 else 0).
Proof.
  induction c; intros P s aa bb ds s' a' b' os Hunused Hnowhile Hsb Heval;
    simpl in *; try (inversion Heval; subst; now eauto).
  - inversion Heval; subst. rewrite t_update_neq; tauto.
  - inversion Heval; subst.
    eapply IHc2; try tauto; [|eassumption].
    eapply IHc1; try tauto; eassumption.
  - inversion Heval; subst; eauto.
    { destruct (beval s be) eqn:Eqbe; inversion H10; inversion H1; subst.
      + eapply IHc1; try tauto; [|eassumption].
        simpl. rewrite Eqbe. rewrite t_update_eq. assumption.
      + eapply IHc2; try tauto; [|eassumption].
        simpl. rewrite Eqbe. rewrite t_update_eq. assumption. }
    { destruct (beval s be) eqn:Eqbe; inversion H10; inversion H1; subst.
      + eapply IHc2; try tauto; [|eassumption].
        simpl. rewrite Eqbe. rewrite t_update_eq. reflexivity.
      + eapply IHc1; try tauto; [|eassumption].
        simpl. rewrite Eqbe. rewrite t_update_eq. reflexivity. }
  - destruct (P x) eqn:Heq.
    + inversion Heval; inversion H10; subst.
      rewrite t_update_neq; try tauto.
      inversion H1; subst; rewrite t_update_neq; tauto.
    + inversion Heval; subst; rewrite t_update_neq; try tauto.
Qed.

(** We now prove that [sel_slh] implies the ideal semantics. *)

(* HIDE: no longer used in [sel_slh_ideal], but maybe still useful (TBD) *)
Lemma spec_unused_same : forall P s a b ds c s' a' b' os x,
  c_unused x c ->
  P |- <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  s' x = s x.
Admitted.

Lemma ideal_unused_update : forall P s a b ds c s' a' b' os x X,
  c_unused x c ->
  P |- <(x !-> X; s, a, b, ds)> =[ c ]=> <(x !-> X; s', a', b', os)> ->
  P |- <(s, a, b, ds)> =[ c ]=> <(x !-> s x; s', a', b', os)>.
Admitted.

Lemma aeval_beval_unused_update : forall X st n, 
  (forall ae, a_unused X ae -> 
    aeval (X !-> n; st) ae = aeval st ae) /\
  (forall be, b_unused X be -> 
    beval (X !-> n; st) be = beval st be).
Proof. 
  intros X st n. apply aexp_bexp_mutind; intros;
  simpl in *; try reflexivity;
  try (
    destruct H1 as [Hau1 Hau2]; apply H in Hau1; apply H0 in Hau2;
    rewrite Hau1; rewrite Hau2; reflexivity
  ).
  (* SOONER: optimize try block so that no 'unused introduction pattern' warning occurs *)
  - rewrite t_update_neq; eauto.
  - destruct H2 as [Hbu Hau]. destruct Hau as [Hau1 Hau2].
    apply H0 in Hau1; apply H1 in Hau2; apply H in Hbu.
    rewrite Hbu; rewrite Hau1; rewrite Hau2. reflexivity.
  - apply H in H0. rewrite H0. reflexivity.
Qed.

Lemma aeval_unused_update : forall X st ae n,
  a_unused X ae ->
  aeval (X !-> n; st) ae = aeval st ae.
Proof. intros X st ae n. apply aeval_beval_unused_update. Qed.

Lemma beval_unused_update : forall X st be n,
  b_unused X be ->
  beval (X !-> n; st) be = beval st be.
  Proof. intros X st be n. apply aeval_beval_unused_update. Qed.

(* HIDE: General statement about total maps. Used to proof ideal_unused_update *)
Lemma submaps_eq_with_update : forall {A} (tm1 tm2 :total_map A) X a,
  (X !-> a; tm1) = (X !-> a; tm2) -> tm1 = (X !-> tm1 X; tm2).
Proof. 
  intros A tm1 tm2 X a H.
  apply FunctionalExtensionality.functional_extensionality.
  intros x; destruct (String.eqb_spec X x) as [Heq | Hneq].
  - rewrite Heq. rewrite t_update_eq. reflexivity.
  - rewrite t_update_neq; [| assumption].
    apply FunctionalExtensionality.equal_f with (x:=x) in H.
    do 2 (rewrite t_update_neq in H; [| assumption]). assumption.
Qed.

Lemma ideal_unused_update_rev_gen : forall P s a b ds c s' a' b' os x X,
  c_unused x c ->
  P |- <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  P |- <(x !-> X; s, a, b, ds)> =[ c ]=> <(x !-> X; s', a', b', os)>.
Proof.
  intros P s a b ds c s' a' b' os x X Hu H.
  induction H; try (now (simpl in *; econstructor; eauto)).
  - simpl in Hu. rewrite t_update_permute; [| tauto].
    econstructor. rewrite aeval_unused_update; tauto.
  - simpl in Hu. destruct Hu as [Hu1 Hu2].
    apply IHideal_eval1 in Hu1. apply IHideal_eval2 in Hu2.
    econstructor; eassumption.
Admitted.

Lemma ideal_unused_update_rev : forall P s a b ds c s' a' b' os x X,
  c_unused x c ->
  P |- <(s, a, b, ds)> =[ c ]=> <(x !-> s x; s', a', b', os)> ->
  P |- <(x !-> X; s, a, b, ds)> =[ c ]=> <(x !-> X; s', a', b', os)>.
Proof.
  intros P s a b ds c s' a' b' os x X Hu H.
  eapply ideal_unused_update_rev_gen in H; [| eassumption].
  rewrite t_update_shadow in H. eassumption.
Qed.

Lemma sel_slh_ideal : forall c P s a (b:bool) ds s' a' (b':bool) os,
  c_unused "b" c ->
  c_no_while c ->
  s "b" = (if b then 1 else 0) ->
  <(s, a, b, ds)> =[ sel_slh P c ]=> <(s', a', b', os)> ->
  P |- <(s, a, b, ds)> =[ c ]=> <("b" !-> s "b"; s', a', b', os)>.
Proof.
  induction c; intros P s aa bb ds s' a' b' os Hunused Hnowhile Hsb Heval;
    simpl in *; inversion Heval; subst.
  - rewrite t_update_same. constructor.
  - rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    constructor. reflexivity.
  - (* seq *) econstructor.
    + apply IHc1; try tauto; eassumption.
    + apply ideal_unused_update_rev; try tauto.
      eapply IHc2; try tauto.
      apply sel_slh_flag in H1; tauto.
  - destruct (beval s be) eqn:Eqbe; inversion H10; inversion H1; subst.
    + eapply IHc1 in H11; try tauto.
      * replace (OBranch true) with (OBranch (beval s be)) by now rewrite <- Eqbe.
        simpl. eapply Ideal_If. rewrite Eqbe.
        simpl in H11. rewrite Eqbe in H11. rewrite t_update_same in H11.
        apply H11.
      * rewrite t_update_eq. simpl. rewrite Eqbe. assumption.
    + eapply IHc2 in H11; try tauto.
      * replace (OBranch false) with (OBranch (beval s be)) by now rewrite <- Eqbe.
        simpl. eapply Ideal_If. rewrite Eqbe.
        simpl in H11. rewrite Eqbe in H11. rewrite t_update_same in H11.
        apply H11.
      * rewrite t_update_eq. simpl. rewrite Eqbe. assumption.
  - (* Ideal_If_F *)
    destruct (beval s be) eqn:Eqbe; inversion H10; inversion H1; subst; simpl in *;
      rewrite Eqbe in H11.
    + replace (OBranch true) with (OBranch (beval s be)) by now rewrite <- Eqbe.
      eapply Ideal_If_F. rewrite Eqbe.
      eapply IHc2 in H11; try tauto. rewrite t_update_eq in H11.
      eapply ideal_unused_update in H11; tauto.
    + replace (OBranch false) with (OBranch (beval s be)) by now rewrite <- Eqbe.
      eapply Ideal_If_F. rewrite Eqbe.
      eapply IHc1 in H11; try tauto. rewrite t_update_eq in H11.
      eapply ideal_unused_update in H11; tauto.
  - tauto.
  - destruct (P x) eqn:Heq; discriminate.
  - destruct (P x) eqn:Heq; discriminate.
  - destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    inversion H1; clear H1; subst. repeat rewrite <- app_nil_end in *.
    inversion H0; clear H0; subst; simpl in *.
    * rewrite t_update_neq; [| tauto]. rewrite Hsb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      rewrite t_update_eq. simpl.
      rewrite <- Hsb at 1. rewrite t_update_same.
      constructor; tauto.
    * rewrite t_update_neq; [| tauto]. rewrite Hsb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      simpl. rewrite <- Hsb at 1. rewrite t_update_same. apply Ideal_ARead_Prot; tauto.
  - destruct (P x) eqn:Heq; discriminate H.
  - destruct (P x) eqn:Heq; discriminate H.
  - destruct (P x) eqn:Heq; discriminate H.
  - destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    constructor; tauto.
  - (* same *)
    destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    constructor; tauto.
  - destruct (P x) eqn:Heq; discriminate H.
  - destruct (P x) eqn:Heq; discriminate H.
  - rewrite t_update_same. constructor; tauto.
  - rewrite t_update_same. constructor; tauto.
Qed.

(** Finally, we use this to prove spec_ct for sel_slh. *)

Theorem sel_slh_spec_ct_secure :
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' b1' b2' os1 os2 ds,
    P ;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    c_unused "b" c ->
    c_no_while c ->
    s1 "b" = 0 ->
    s2 "b" = 0 ->
    <(s1, a1, false, ds)> =[ sel_slh P c ]=> <(s1', a1', b1', os1)> ->
    <(s2, a2, false, ds)> =[ sel_slh P c ]=> <(s2', a2', b2', os2)> ->
    os1 = os2.
Proof.
  intros P PA c s1 s2 a1 a2 s1' s2' a1' a2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Hunused Hnowhile Hs1b Hs2b Heval1 Heval2.
  eapply sel_slh_ideal in Heval1; try assumption.
  eapply sel_slh_ideal in Heval2; try assumption.
  eapply ideal_spec_ct_secure; eauto.
Qed.

(* HIDE: The less useful for security direction of the idealized semantics being
   equivalent to [sel_slh]; easier to prove even for while (forwards compiler
   correctness). *)

Lemma spec_seq_assoc3 : forall st ast b ds c1 c2 c3 st' ast' b' os,
  <( st, ast, b, ds )> =[ c1; c2; c3 ]=> <( st', ast', b', os )> ->
  <( st, ast, b, ds )> =[ (c1; c2); c3 ]=> <( st', ast', b', os )>.
Admitted.

Lemma spec_seq_assoc4 : forall st ast b ds c1 c2 c3 c4 st' ast' b' os,
  <( st, ast, b, ds )> =[ c1; c2; c3; c4 ]=> <( st', ast', b', os )> ->
  <( st, ast, b, ds )> =[ (c1; c2; c3); c4 ]=> <( st', ast', b', os )>.
Admitted.

Lemma ideal_sel_slh : forall P s a b ds c s' a' b' os,
  c_unused "b" c ->
  P |- <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  <("b" !-> (if b then 1 else 0); s, a, b, ds)> =[ sel_slh P c ]=>
    <("b" !-> (if b' then 1 else 0); s', a', b', os)>.
Proof.
  intros P s a b ds c s' a' b' os Hunused Heval.
  induction Heval; simpl in *.
  - constructor.
  - destruct Hunused as [Hx He].
    rewrite t_update_permute; [| assumption].
    apply Spec_Asgn. rewrite aeval_unused_update; assumption.
  - eapply Spec_Seq.
    + eapply IHHeval1. tauto.
    + eapply IHHeval2. tauto.
  - replace (beval st be) with (beval ("b" !-> (if b then 1 else 0); st) be)
      by (apply beval_unused_update; tauto).
    apply Spec_If. rewrite beval_unused_update; [| tauto].
    destruct (beval st be) eqn:Eqbeval.
    + replace ds with ([]++ds)%list by reflexivity.
      replace os1 with ([]++os1)%list by reflexivity.
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_same. apply IHHeval. tauto.
    + (* same *)
      replace ds with ([]++ds)%list by reflexivity.
      replace os1 with ([]++os1)%list by reflexivity.
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_same. apply IHHeval. tauto.
  - replace (beval st be) with (beval ("b" !-> (if b then 1 else 0); st) be)
      by (apply beval_unused_update; tauto).
    apply Spec_If_F. rewrite beval_unused_update; [| tauto].
    destruct (beval st be) eqn:Eqbeval.
    + replace ds with ([]++ds)%list by reflexivity.
      replace os1 with ([]++os1)%list by reflexivity.
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_shadow. apply IHHeval. tauto.
    + (* same *)
      replace ds with ([]++ds)%list by reflexivity.
      replace os1 with ([]++os1)%list by reflexivity.
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_shadow. apply IHHeval. tauto.
  - (* while (most difficult case); it works though
       - proved mispeculation subcase, and the other case should be the same
       - SOONER: clean up the proof of the mispeculation subcase before copy pasting *)
    assert(G : b_unused "b" be /\
      (c_unused "b" c /\ b_unused "b" be /\ c_unused "b" c) /\ True) by tauto.
    specialize (IHHeval G). clear G.
    inversion IHHeval; clear IHHeval; subst. (* Spec_If *)
    + replace (DStep :: ds0) with ((DStep :: ds0)++[])%list by apply app_nil_r.
      replace (OBranch (beval ("b" !-> (if b then 1 else 0); st) be) :: os1)
        with ((OBranch (beval ("b" !-> (if b then 1 else 0); st) be) :: os1)++[])%list
        by apply app_nil_r.
      eapply Spec_Seq.
      * apply Spec_While. apply Spec_If.
        rewrite beval_unused_update; [| tauto].
        destruct (beval ("b" !-> (if b then 1 else 0); st)) eqn:Eqbeval; admit.
      * constructor. simpl. admit.
    + (* mispeculated while *)
      rewrite beval_unused_update in H10; try tauto.
      destruct (beval st be) eqn:Eqbeval.
      * inversion H10; inversion H11; subst.
        replace (DForce :: ds1 ++ [])%list
          with ([DForce] ++ ds1)%list by (rewrite app_nil_r; reflexivity).
        replace (OBranch (beval ("b" !-> (if b then 1 else 0); st) be) :: os0 ++ [])
          with ([OBranch (beval ("b" !-> (if b then 1 else 0); st) be)] ++ os0)%list
          by (rewrite app_nil_r; reflexivity).
        eapply Spec_Seq; [| eassumption].
        apply Spec_While. apply Spec_If_F.
        rewrite beval_unused_update; [| tauto].
        rewrite Eqbeval. apply Spec_Skip.
      * rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply spec_seq_assoc4 in H10.
        inversion H10; subst.
        replace (DForce :: ds1 ++ ds2)%list
          with ((DForce :: ds1) ++ ds2)%list by reflexivity.
        replace (OBranch false :: os0 ++ os2)%list
          with ((OBranch false :: os0) ++ os2)%list by reflexivity.
        eapply Spec_Seq; [| eassumption].
        apply Spec_While.
        (* going back and forth *)
        replace (OBranch false) with (OBranch (beval ("b" !-> (if b then 1 else 0); st) be))
          by now (rewrite beval_unused_update; [| tauto]; rewrite <- Eqbeval).
        eapply Spec_If_F. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply spec_seq_assoc3. assumption.
  - rewrite t_update_permute; [| tauto]. destruct (P x) eqn:EqPx.
    * replace [DStep] with ([DStep]++[])%list by apply app_nil_r.
      replace [OARead a i] with ([OARead a i]++[])%list by apply app_nil_r.
      eapply Spec_Seq.
      { apply Spec_ARead; [| tauto]. rewrite aeval_unused_update; tauto. }
      { assert (G : (x !-> nth i (ast a) 0; "b" !-> 0; st) =
                    (x !-> aeval (x !-> nth i (ast a) 0; "b" !-> 0; st)
                                 <{{("b" = 1) ? 0 : x}}>;
                    x !-> nth i (ast a) 0; "b" !-> 0; st)).
        { simpl. rewrite t_update_neq; [|tauto]. rewrite t_update_eq. simpl.
          rewrite t_update_same. reflexivity. }
        rewrite G at 2. apply Spec_Asgn. reflexivity. }
    * apply Spec_ARead; [| tauto]. rewrite aeval_unused_update; tauto.
  - rewrite H. unfold secret. rewrite t_update_permute; [| tauto].
    apply Spec_ARead_U; try tauto. rewrite aeval_unused_update; tauto.
  - rewrite H. unfold public.
    replace [DLoad a' i'] with ([DLoad a' i']++[])%list by apply app_nil_r.
    replace [OARead a i] with ([OARead a i]++[])%list by apply app_nil_r.
    eapply Spec_Seq.
    + apply Spec_ARead_U; try tauto. rewrite aeval_unused_update; tauto.
    + assert (G : ("b" !-> 1; x !-> 0; st) =
                  (x !-> aeval (x !-> nth i' (ast a') 0; "b" !-> 1; st)
                               <{{("b" = 1) ? 0 : x}}>;
                   x !-> nth i' (ast a') 0; "b" !-> 1; st)).
      { simpl. rewrite t_update_neq; [|tauto]. rewrite t_update_eq. simpl.
        rewrite t_update_permute; [| tauto]. rewrite t_update_shadow. reflexivity. }
      rewrite G. simpl. apply Spec_Asgn. reflexivity.
  - constructor; try rewrite aeval_unused_update; tauto.
  - constructor; try rewrite aeval_unused_update; tauto.
Admitted. (* only a symmetric case left for properly speculated while loops *)

(* HIDE: Moving syntactic constraints about ds and os out of the conclusions of
   rules and into equality premises could make this proof script less
   verbose. Maybe just define "smart constructors" for that? *)
