(** * SpecCT: Speculative Constant Time *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From Coq Require Import List. Import ListNotations.
From PLF Require Export StaticIFC.
Set Default Goal Selector "!".

Definition FILL_IN_HERE := <{True}>.
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

Inductive com' : Type :=
  | Skip
  | Asgn (x : string) (e : aexp)
  | Seq (c1 c2 : com')
  | If (b : bexp) (c1 c2 : com')
  | While (b : bexp) (c : com')
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

(* SOONER: CH: Maybe a good way to get the best of both worlds would
   be to use a type system to combine the two states into one, yet to
   keep accessing the arrays only with the special ARead and AWrite
   operations above. This would make this part of the chapter depend
   on types, while currently we manged to avoid that dependency, at
   the cost of duplicating the state. If avoiding the dependency is
   important we could dynamically prevent nat vs array type confusion
   for now and only return later to prevent it using static typing? *)

(* TERSE: HIDEFROMHTML *)
Declare Custom Entry com'.
Declare Scope com'_scope.

Notation "<{{ e }}>" := e (at level 0, e custom com' at level 99) : com'_scope.
Notation "( x )" := x (in custom com', x at level 99) : com'_scope.
Notation "x" := x (in custom com' at level 0, x constr at level 0) : com'_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com' at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com'_scope.

Open Scope com'_scope.

Notation "'skip'"  :=
  Skip (in custom com' at level 0) : com'_scope.
Notation "x := y"  :=
  (Asgn x y)
    (in custom com' at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com'_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com' at level 90, right associativity) : com'_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (in custom com' at level 89, x custom com at level 99,
     y at level 99, z at level 99) : com'_scope.
Notation "'while' x 'do' y 'end'" :=
  (While x y)
    (in custom com' at level 89, x custom com at level 99, y at level 99) : com'_scope.

(* HIDE *)
Check <{{ skip }}>.
Check <{{ (skip ; skip) ; skip }}>.
Check <{ 1 + 2 }>.
Check <{ 2 = 1 }>.
Check <{{ Z := X }}>.
Check <{{ Z := X + 3 }}>.
Definition func (c : com') : com' := <{{ c ; skip }}>.
Check <{{ skip; func <{{ skip }}> }}>.
Definition func2 (c1 c2 : com') : com' := <{{ c1 ; c2 }}>.
Check <{{ skip ; func2 <{{skip}}> <{{skip}}> }}>.
Check <{ true && ~(false && true) }>.
Check <{{ if true then skip else skip end }}>.
Check <{{ if true && true then skip; skip else skip; X:=X+1 end }}>.
Check <{{ while Z <> 0 do Y := Y * Z; Z := Z - 1 end }}>.
(* /HIDE *)

Notation "x '<-' a '[[' i ']]'"  :=
  (ARead x a i)
     (in custom com' at level 0, x constr at level 0,
      a at level 85, i custom com at level 85, no associativity) : com'_scope.
Notation "a '[' i ']'  '<-' e"  :=
  (AWrite a i e)
     (in custom com' at level 0, a constr at level 0,
      i custom com at level 0, e custom com at level 85,
         no associativity) : com'_scope.

Definition astate := total_map (list nat).

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

(** We define an instrumented operational semantics based on these
   observations. *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation
         "'(' st , ast ')' '=[' c ']=>' '(' stt , astt , os ')'"
         (at level 40, c custom com' at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive cteval : com' -> state -> astate -> state -> astate -> obs -> Prop :=
  | CTE_Skip : forall st ast,
      (st , ast) =[ skip ]=> (st, ast, [])
  | CTE_Asgn  : forall st ast e n x,
      aeval st e = n ->
      (st, ast) =[ x := e ]=> (x !-> n; st, ast, [])
  | CTE_Seq : forall c1 c2 st ast st' ast' st'' ast'' os1 os2,
      (st, ast) =[ c1 ]=> (st', ast', os1)  ->
      (st', ast') =[ c2 ]=> (st'', ast'', os2) ->
      (st, ast)  =[ c1 ; c2 ]=> (st'', ast'', os1++os2)
  | CTE_IfTrue : forall st ast st' ast' b c1 c2 os1,
      beval st b = true ->
      (st, ast) =[ c1 ]=> (st', ast', os1) ->
      (st, ast) =[ if b then c1 else c2 end]=> (st', ast', OBranch true::os1)
  | CTE_IfFalse : forall st ast st' ast' b c1 c2 os1,
      beval st b = false ->
      (st, ast) =[ c2 ]=> (st', ast', os1) ->
      (st, ast) =[ if b then c1 else c2 end]=> (st', ast', OBranch false::os1)
  | CTE_WhileFalse : forall b st ast c,
      beval st b = false ->
      (st,ast) =[ while b do c end ]=> (st, ast, [OBranch false])
  | CTE_WhileTrue : forall st st' st'' ast ast' ast'' b c os' os'',
      beval st b = true ->
      (st, ast)  =[ c ]=> (st', ast', os') ->
      (st', ast') =[ while b do c end ]=> (st'', ast'', os'') ->
      (st, ast)  =[ while b do c end ]=> (st'', ast'', OBranch true::os'++os'')
  | CTE_ARead : forall st ast x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      (st, ast) =[ x <- a[[ie]] ]=> (x !-> nth i (ast a) 0; st, ast, [OARead a i])
  | CTE_Write : forall st ast a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      (st, ast) =[ a[ie] <- e ]=> (st, a !-> upd i (ast a) n; ast, [OAWrite a i])

  where "( st , ast ) =[ c ]=> ( stt , astt , os )" := (cteval c st ast stt astt os).
(* TERSE: /HIDEFROMHTML *)

(** *** Type system for cryptographic constant-time programming *)

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

Inductive ct_well_typed (P:pub_vars) (PA:pub_arrs) : com' -> Prop :=
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
    P;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    (s1, a1) =[ c ]=> (s1', a1', os1) ->
    (s2, a2) =[ c ]=> (s2', a2', os2) ->
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
  - split; auto.
  - rewrite (noninterferent_bexp Heq H12) in H.
    rewrite H in H2. discriminate H2.
  - rewrite (noninterferent_bexp Heq H10) in H.
    rewrite H in H7. discriminate H7.
  - edestruct IHHeval1_2; eauto.
    + eapply IHHeval1_1; eauto.
    + eapply IHHeval1_1; eauto.
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
    P;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    (s1, a1) =[ c ]=> (s1', a1', os1) ->
    (s2, a2) =[ c ]=> (s2', a2', os2) ->
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
  - reflexivity.
  - rewrite (noninterferent_bexp Heq H12) in H.
    rewrite H in H2. discriminate H2.
  - rewrite (noninterferent_bexp Heq H10) in H.
    rewrite H in H7. discriminate H7.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
    + eapply ct_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption | eassumption ];
        eassumption.
    + eapply ct_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption | eassumption ];
        eassumption.
  - (* NEW CASE: ARead *)
    f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* NEW CASE: AWrite *)
    f_equal. f_equal. eapply noninterferent_aexp; eassumption.
Qed.
(* /FOLD *)

(** ** Speculative constant time *)

(** The observations are the same, so we can just reuse them. *)
Print observation.

Inductive direction :=
| DStep
| DForce
| DLoad (a : string) (i : nat)
| DStore (a : string) (i : nat).

Definition dirs := list direction.

Reserved Notation
         "'(' st , ast , ds ')' '=[' c ']=>' '(' stt , astt , os ')'"
         (at level 40, c custom com' at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive spec_eval : com' -> state -> astate -> state -> astate -> obs -> dirs -> Prop :=
  | Spec_Skip : forall st ast,
      (st, ast, [DStep]) =[ skip ]=> (st, ast, [])
  | Spec_Asgn  : forall st ast e n x,
      aeval st e = n ->
      (st, ast, [DStep]) =[ x := e ]=> (x !-> n; st, ast, [])
  | Spec_Seq : forall c1 c2 st ast st' ast' st'' ast'' os1 os2 ds1 ds2,
      (st, ast, ds1) =[ c1 ]=> (st', ast', os1)  ->
      (st', ast', ds2) =[ c2 ]=> (st'', ast'', os2) ->
      (st, ast, ds1++ds2)  =[ c1 ; c2 ]=> (st'', ast'', os1++os2)
  | Spec_If : forall st ast st' ast' b c1 c2 os1 ds,
      (st, ast, ds) =[ match beval st b with
                       | true => c1
                       | false => c2 end ]=> (st', ast', os1) ->
      (st, ast, DStep :: ds) =[ if b then c1 else c2 end ]=>
      (st', ast', OBranch (beval st b)::os1)
  | Spec_If_F : forall st ast st' ast' b c1 c2 os1 ds,
      (st, ast, ds) =[ match beval st b with
                       | true => c2 (* <-- branches swapped *)
                       | false => c1 end ]=> (st', ast', os1) ->
      (st, ast, DForce :: ds) =[ if b then c1 else c2 end ]=>
      (st', ast', OBranch (beval st b)::os1)
  | Spec_WhileFalse : forall b st ast c,
      beval st b = false ->
      (st, ast, [DStep]) =[ while b do c end ]=> (st, ast, [OBranch false])
  | Spec_WhileFalse_F : forall st st' st'' ast ast' ast'' b c os' os'' ds ds',
      beval st b = false ->
      (st, ast, ds)  =[ c ]=> (st', ast', os') ->
      (st', ast', ds') =[ while b do c end ]=> (st'', ast'', os'') ->
      (st, ast, DForce::ds++ds') =[ while b do c end ]=> (st'', ast'', OBranch false::os'++os'')
  | Spec_WhileTrue : forall st st' st'' ast ast' ast'' b c os' os'' ds ds',
      beval st b = true ->
      (st, ast, ds)  =[ c ]=> (st', ast', os') ->
      (st', ast',ds') =[ while b do c end ]=> (st'', ast'', os'') ->
      (st, ast, DStep::ds++ds')  =[ while b do c end ]=> (st'', ast'', OBranch true::os'++os'')
  | Spec_WhileTrue_F : forall b st ast c,
      beval st b = true ->
      (st, ast, [DForce]) =[ while b do c end ]=> (st, ast, [OBranch true])
  | Spec_ARead : forall st ast x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      (st, ast, [DStep]) =[ x <- a[[ie]] ]=> (x !-> nth i (ast a) 0; st, ast, [OARead a i])
  | Spec_ARead_U : forall st ast x a ie i a' i',
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      (st, ast, [DLoad a' i']) =[ x <- a[[ie]] ]=> (x !-> nth i' (ast a') 0; st, ast, [OARead a i])
  | Spec_Write : forall st ast a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      (st, ast, [DStep]) =[ a[ie] <- e ]=> (st, a !-> upd i (ast a) n; ast, [OAWrite a i])
  | Spec_Write_U : forall st ast a ie i e n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      (st, ast, [DStore a' i']) =[ a[ie] <- e ]=> (st, a' !-> upd i' (ast a') n; ast, [OAWrite a i])

  where "( st , ast , ds ) =[ c ]=> ( stt , astt , os )" := (spec_eval c st ast stt astt os ds).

(* HIDE: Add fences and maybe speculation bit *)

Definition spec_ct_secure :=
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2 ds,
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    (s1, a1, ds) =[ c ]=> (s1', a1', os1) ->
    (s2, a2, ds) =[ c ]=> (s2', a2', os2) ->
    os1 = os2.
