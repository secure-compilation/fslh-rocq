(** * SpecCT: Speculative Constant-Time *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(** ** Cryptographic constant-time *)

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

(** *** Constant-time conditional *)

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

(** *** Typing Constant-time conditional *)

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

(** *** Now back to adding arrays *)
(* /HIDE *)

Inductive com : Type :=
  | Skip
  | Asgn (x : string) (e : aexp)
  | Seq (c1 c2 : com)
  | If (b : bexp) (c1 c2 : com)
  | While (b : bexp) (c : com)
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

(** *** Observations *)

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

(** *** Type system for cryptographic constant-time programming *)

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

Scheme aexp_bexp_ind := Induction for aexp_has_label Sort Prop
with bexp_aexp_ind := Induction for bexp_has_label Sort Prop.
Combined Scheme aexp_bexp_mutind from aexp_bexp_ind,bexp_aexp_ind.

Theorem noninterferent_aexp_bexp : forall P s1 s2,
  pub_equiv P s1 s2 ->
  (forall a l, P |-a- a \in l ->
   l = public -> aeval s1 a = aeval s2 a) /\
  (forall b l, P |-b- b \in l ->
   l = public -> beval s1 b = beval s2 b).
Proof.
  intros P s1 s2 Heq. apply (aexp_bexp_mutind P);
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
  | CT_Com :
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

(** *** Final theorems *)

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

(** ** Speculative constant-time *)

(** The observations are the same, so we can just reuse them. *)
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
      <(st, ast, b, [DStep])> =[ skip ]=> <(st, ast, b, [])>
  | Spec_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      <(st, ast, b, [DStep])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
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
  | Spec_ARead : forall st ast b x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      <(st, ast, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i (ast a) 0; st, ast, b, [OARead a i])>
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
   our big-step semantics can't be distinguished from non-termination. This is
   probably not a problem, but just wanted to mention it. *)

(** Without fences the speculation bit [b] is just a form of instrumentation
    that doesn't affect the semantics, except adding more stuckness for the [_U] rules. *)

(* LATER: Could also add fences, but they are not needed for SLH. They would add
   a bit of complexity to the big-step semantics, since they behave like a halt
   instruction that prematurely ends execution, which means adding at least one
   more rule for sequencing (basically an error monad, but with a (halt) bit of
   cleverness we can probably avoid extra rules for if and while, since we're
   just threading through things). We likely don't want to treat this stuckness
   as not producing a final state though, since a stuck fence should be final
   state in their small-step semantics (actually the messed that up,
   see next point). *)

(* LATER: Could prove this semantics equivalent to the small-step one from the
   two IEEE SP 2023 papers. The fact that their rule [Seq-Skip] requires a step
   seems wrong if first command in the sequence is already skip. Also the way
   they define final results seem wrong for stuck fences, and that would either
   need to be fixed to include stuck fences deep inside or to bubble up stuck
   fences to the top (error monad, see prev point). *)

(* LATER: Could add the declassify construct from Spectre Declassified, but for
   now trying to keep things simple. If we add that then the RNI notion of
   Definition 2 relies on the small-step semantics to stop at the first force
   directive. Doing that with a big-step semantics seems trickier. We could
   build a version that halts early on the first force? *)

(* HIDE: Just to warm up formalized the first lemma in the Spectre Declassified
   paper: Lemma 1: structural properties of execution *)

Lemma speculation_bit_monotonic : forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = true ->
  b' = true.
Proof. intros c s a b ds s' a' b' os Heval Hb. induction Heval; eauto. Qed.

(* HIDE: This one is weaker for big-step semantics *)
Lemma speculation_needs_force : forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = false ->
  b' = true ->
  In DForce ds.
Proof.
  intros c s a b ds s' a' b' os Heval Hb Hb'.
  induction Heval; subst; simpl; eauto; try discriminate.
  - apply in_or_app. destruct b'.
    + left. apply IHHeval1; reflexivity.
    + right. apply IHHeval2; reflexivity.
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

Definition seq_eval (c:com) (s:state) (a:astate) (b:bool)
  (s':state) (a':astate) (b':bool) (os:obs) : Prop :=
  exists ds, (forall d, In d ds -> d = DStep) /\
    <(s, a, false, ds)> =[ c ]=> <(s', a', b', os)>.

(* LATER: We should be able to prove that [cteval] and [seq_eval] coincide, so
   by [ct_well_typed_ct_secure] also directly get their Lemma 2. *)

(** *** Speculative constant-time security definition *)

Definition spec_ct_secure :=
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' b1' b2' os1 os2 ds,
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    <(s1, a1, false, ds)> =[ c ]=> <(s1', a1', b1', os1)> ->
    <(s2, a2, false, ds)> =[ c ]=> <(s2', a2', b2', os2)> ->
    os1 = os2.

(** Selective SLH transformation that we will show enforces speculative constant-time *)

Open Scope string_scope.

Fixpoint sel_slh (P:pub_vars) (c:com) :=
  match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ sel_slh P c1; sel_slh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if be then "b" := (be ? "b" : 1); sel_slh P c1
               else "b" := (be ? 1 : "b"); sel_slh P c1 end}}>
  | <{{while be do c end}}> =>
      <{{while be do "b" := (be ? "b" : 1); sel_slh P c end;
         "b" := (be ? 1 : "b")}}>
  | <{{x <- a[[i]]}}> =>
      if P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
             else <{{x <- a[[i]]}}>
  | <{{a[i] <- e}}> => <{{a[i] <- e}}>
  end.

Close Scope string_scope.

(** To prove this transformation secure Spectre Declassified uses an idealized semantics *)

Reserved Notation
         "P '|-' '<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval (P:pub_vars) :
    com -> state -> astate -> bool -> dirs ->
           state -> astate -> bool -> obs -> Prop :=
  | Ideal_Skip : forall st ast b,
      P |- <(st, ast, b, [DStep])> =[ skip ]=> <(st, ast, b, [])>
  | Ideal_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      P |- <(st, ast, b, [DStep])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
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
      P |- <(st, ast, false, [DStep])> =[ x <- a[[ie]] ]=>  (* <-- NEW: only for sequential executions *)
        <(x !-> nth i (ast a) 0; st, ast, false, [OARead a i])>
  | Ideal_ARead_U : forall st ast x a ie i a' i',
      P x = secret -> (* <-- NEW: this rule applies now only for loads into secret variables *)
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <(st, ast, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i' (ast a') 0; st, ast, true, [OARead a i])>
  | Ideal_ARead_Prot : forall st ast x a ie i,
      P x = public ->  (* <-- NEW: new rule for loads into public variables *)
      aeval st ie = i ->
      P |- <(st, ast, true, [DStep])> =[ x <- a[[ie]] ]=>
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

(* SOONER: Show that on sequential executions this is equivalent to [seq_eval] (Lemma 3) *)

(** Let's now prove that the idealized semantics does enforce speculative constant-time *)

Definition prefix {X:Type} (xs ys : list X) : Prop :=
  exists zs, xs = ys ++ zs.

Lemma prefix_refl : forall {X:Type} {ds : list X},
  prefix ds ds.
Proof. intros X ds. exists []. apply app_nil_end. Qed.

Lemma prefix_app : forall {X:Type} {ds1 ds2 ds0 ds3 : list X},
  prefix (ds1 ++ ds2) (ds0 ++ ds3) ->
  prefix ds1 ds0 \/ prefix ds0 ds1.
Admitted.

Lemma prefix_cons : forall {X:Type} {d : X} {ds2 ds3 : list X},
  prefix (d :: ds2) (d :: ds3) ->
  prefix ds2 ds3.
Admitted.

Lemma prefix_append_front : forall {X:Type} {ds1 ds2 ds3 : list X},
  prefix (ds1 ++ ds2) (ds1 ++ ds3) ->
  prefix ds2 ds3.
Admitted.

Lemma app_eq_prefix : forall {X:Type} {ds1 ds2 ds1' ds2' : list X},
  ds1 ++ ds2 = ds1' ++ ds2' ->
  prefix ds1 ds1' \/ prefix ds1' ds1.
Admitted.

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
      (b1' = false -> pub_equiv PA a1' a2') /\ ds1 = ds2.
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
    { destruct Hds as [Hds | Hds]; apply prefix_app in Hds; tauto.}
    assert (ds1 = ds0). { eapply IHHeval1_1; eassumption.} subst. f_equal.
    assert (Hds2: prefix ds2 ds3 \/ prefix ds3 ds2).
    { destruct Hds as [Hds | Hds]; apply prefix_append_front in Hds; tauto.}
    (* TODO: proofs above and below can be better integrated *)
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
  - (* if contra *) unfold prefix in Hds.
    destruct Hds as [ [zs Hds] | [zs Hds] ]; simpl in Hds; inversion Hds.
  - (* if contra *) unfold prefix in Hds.
    destruct Hds as [ [zs Hds] | [zs Hds] ]; simpl in Hds; inversion Hds.
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
        { unfold prefix in Hds.
          destruct Hds as [ [zs Hds] | [zs Hds] ]; simpl in Hds;
            inversion Hds; reflexivity. }
        { now destruct (PA a).}
      * do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
        apply Heq. apply Hy.
    + unfold prefix in Hds.
      destruct Hds as [ [zs Hds] | [zs Hds] ]; simpl in Hds; inversion Hds; reflexivity.
  - (* array read contra *) unfold prefix in Hds.
    destruct Hds as [ [zs Hds] | [zs Hds] ]; simpl in Hds; inversion Hds.
  - (* array read contra *) unfold prefix in Hds.
    destruct Hds as [ [zs Hds] | [zs Hds] ]; simpl in Hds; inversion Hds.
  - (* array read (ARead_Prot) *) split4; eauto.
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
  - (* array write contra *) unfold prefix in Hds.
    destruct Hds as [ [zs Hds] | [zs Hds] ]; simpl in Hds; inversion Hds.
  - (* array write contra *) unfold prefix in Hds.
    destruct Hds as [ [zs Hds] | [zs Hds] ]; simpl in Hds; inversion Hds.
  - (* array write (Write_U) *) split4; eauto.
    + intro contra. discriminate contra.
    + unfold prefix in Hds.
      destruct Hds as [ [zs Hds] | [zs Hds] ]; simpl in Hds; inversion Hds; reflexivity.
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
    { eapply ct_well_typed_ideal_noninterferent; [ | | | eassumption | eassumption]; eauto.}
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
  - (* ARead_U *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* ARead_Prot *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* AWrite *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* AWrite *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
Qed.

(* SOONER: Prove that the idealized semantics is equivalent to [sel_slh]
   transformation (Lemma 6 and the more precise Lemma 7). Unclear if we need to
   define any erasure function, since in our semantics we already erased the
   silent observations by working with observation lists and adding nothing to
   them for silent observations. That's convenient. Q: Is that correct though?
   Or does it weaken our attacker model and we need to switch to options? *)

(** SOONER: All results about [sel_slh] will have to assume that [c] doesn't
    already use the variable ["b"] ... see below: *)

Open Scope string_scope.

Lemma ideal_sel_slh : forall P s a b ds c s' a' b' os,
  P |- <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  <("b" !-> (if b then 1 else 0); s, a, b, ds)> =[ sel_slh P c ]=>
    <("b" !-> (if b' then 1 else 0); s', a', b', os)>.
Proof.
  intros P s a b ds c s' a' b' os Heval. induction Heval; simpl.
  - constructor.
  - rewrite t_update_permute.
    + apply Spec_Asgn. admit. (* only correct if "b" is not used *)
    + admit. (* again, x shouldn't be "b" *)
Admitted.

Lemma sel_slh_ideal : forall P s a (b:bool) ds c s' a' (b':bool) os,
  <("b" !-> (if b then 1 else 0); s, a, b, ds)> =[ sel_slh P c ]=>
    <("b" !-> (if b' then 1 else 0); s', a', b', os)> ->
  P |- <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)>.
Admitted.
