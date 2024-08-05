(** * UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From SECF Require Import SpecCT.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(** * Relative security *)

(** We would like to also enforce security for arbitrary programs that are do
    not follow the cryptographic constant time programming discipline
    (i.e. which do not satisfy [ct_well_typed]). The goal is to achieve a
    relative notion of security which intuitively ensures that the protected
    program does not leak more information speculatively than the original
    program leaks sequentially via the CT observations. One way to achieve this
    protection is by transforming the program using Ultimate Speculative Load
    Hardening (USLH), instead of the selective variant from the previous chapter. *)

(** We formalize this as a relative security property that doesn't label data at
    all as public or secret. *)

Definition seq_obs_secure c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2,
    <(st1, ast1)> =[ c ]=> <(stt1, astt1, os1)> ->
    <(st2, ast2)> =[ c ]=> <(stt2, astt2, os2)> ->
    os1 = os2.

Definition spec_obs_secure c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure (trans : com -> com) (c:com) (st1 st2:state) : Prop :=
  forall ast1 ast2,
    seq_obs_secure c st1 st2 ast1 ast2 ->
    spec_obs_secure (trans c) st1 st2 ast1 ast2.

(** Additional Property on [astaste]'s *)

Definition nonempty_arrs (ast :astate) :Prop :=
  forall a, 0 < length (ast a).

(** * Ultimate Speculative Load Hardening *)

Fixpoint ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ ultimate_slh c1; ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c1
                          else "b" := ("b" = 0 && be) ? 1 : "b"; ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c end;
         "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

Reserved Notation
         "'|-i' '<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval :
    com -> state -> astate -> bool -> dirs ->
           state -> astate -> bool -> obs -> Prop :=
  | Ideal_Skip : forall st ast b,
      |-i <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Ideal_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      |-i <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Ideal_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      |-i <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      |-i <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      |-i <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os2++os1)>
  | Ideal_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      |-i <(st, ast, b, ds)> =[ match negb b && beval st be  with
                                 | true => c1
                                 | false => c2 end ]=> <(st', ast', b', os1)> ->
      |-i <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', os1++[OBranch (negb b && beval st be)])>
  | Ideal_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      |-i <(st, ast, true, ds)> =[ match negb b && beval st be  with
                                 | true => c2 (* <-- branches swapped *)
                                 | false => c1 end ]=> <(st', ast', b', os1)> ->
      |-i <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', os1++[OBranch (negb b && beval st be)])>
  | Ideal_While : forall be st ast b ds st' ast' b' os c,
      |-i <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      |-i <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Ideal_ARead : forall st ast (b :bool) x a ie i,
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      |-i <(st, ast, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i (ast a) 0; st, ast, b, [OARead a i])>
  | Ideal_Write : forall st ast (b :bool) a ie i e n,
      aeval st e = n ->
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      |-i <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (ast a) n; ast, b, [OAWrite a i])>

  where "|-i <( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (ideal_eval c st ast b ds stt astt bb os).

Fixpoint observations (c:com) (ds:dirs) : option (obs * dirs) :=
  match c with
  | <{{skip}}> => Some ([],ds)
  | <{{x := e}}> => Some ([],ds)
  | <{{c1; c2}}> =>
      match observations c1 ds with
      | Some (os',ds') =>
          match observations c2 ds' with
          | Some (os'',ds'') => Some (os''++os', ds'')
          | None => None
          end
      | None => None
      end
  | <{{if be then c1 else c2 end}}> =>
      match ds with
      | DStep :: ds' =>
          match observations c2 ds' with
          | Some (os,ds'') => Some (os++[OBranch false],ds'')
          | None => None
          end
      | DForce :: ds' =>
          match observations c1 ds' with
          | Some (os,ds'') => Some (os++[OBranch true],ds'')
          | None => None
          end
      | _ => None
      end
  | <{{while be do c end}}> =>
      match ds with
      | DStep :: ds' => Some ([OBranch false],ds')
      | DForce :: ds' =>
          match observations c (* <- should actually be: while be do c end *) ds' with
          | Some (os,ds'') => Some (os++[OBranch true],ds'')
          | None => None
          end
      | _ => None
      end
  | <{{x <- a[[i]]}}> => Some ([OARead a 0],ds)
  | <{{a[i] <- e}}> => Some ([OAWrite a 0],ds)
  end.

Lemma observations_fixed : forall c st ast ds stt astt os,
  unused "b" c ->
  st "b" = 1 ->
  |-i <(st, ast, true, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  Some (os,[]) = observations c ds.
Admitted.

Lemma gilles_lemma : forall c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2,
  unused "b" c ->
  st1 "b" = 1 ->
  st2 "b" = 1 ->
  |-i <(st1, ast1, true, ds)> =[ c ]=> <(stt1, astt1, true, os1)> ->
  |-i <(st2, ast2, true, ds)> =[ c ]=> <(stt2, astt2, true, os2)> ->
  os1 = os2.
Proof.
  intros c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2 Hunused Hb1 Hb2 H1 H2.
  apply observations_fixed in H1; try auto.
  apply observations_fixed in H2; try auto. congruence.
Qed.

Definition ideal_obs_secure c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    |-i <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    |-i <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Lemma relative_noninterference : forall c st1 st2 ast1 ast2,
  unused "b" c ->
  st1 "b" = 1 ->
  st2 "b" = 1 ->
  seq_obs_secure c st1 st2 ast1 ast2 ->
  ideal_obs_secure c st1 st2 ast1 ast2.
Proof.
Admitted.

Lemma ideal_unused_update : forall st ast b ds c st' ast' b' os X n,
  unused X c ->
  |-i <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)> ->
  |-i <(st, ast, b, ds)> =[ c ]=> <(X !-> st X; st', ast', b', os)>.
Proof.
Admitted.

Lemma ideal_unused_update_rev : forall st ast b ds c st' ast' b' os X n,
  unused X c ->
  |-i <(st, ast, b, ds)> =[ c ]=> <(X!-> st X; st', ast', b', os)> ->
  |-i <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)>.
Proof.
Admitted.

Lemma spec_eval_preserves_nonempty_arrs : forall c st ast b ds st' ast' b' os,
  nonempty_arrs ast ->
  <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  nonempty_arrs ast'.
Admitted.

Lemma flag_zero_check_spec_bit : forall (st :state) (X :string) (b b' :bool), 
  st X = (if b then 1 else 0) ->
  (st X =? 0)%nat = b' ->
  b = negb b'.
Proof.
 intros st X b b' Hflag Heqb. destruct b; destruct b'; try reflexivity;
 rewrite Hflag in Heqb; simpl in Heqb; discriminate.
Qed.

Lemma flag_one_check_spec_bit : forall (st :state) (X :string) (b b' :bool), 
  st X = (if b then 1 else 0) ->
  (st X =? 1)%nat = b' ->
  b = b'.
Proof.
 intros st X b b' Hflag Heqb. destruct b; destruct b'; try reflexivity;
 rewrite Hflag in Heqb; simpl in Heqb; discriminate.
Qed.


Definition ultimate_slh_flag_prop (c :com) (ds :dirs) :Prop :=
  forall st ast (b:bool) st' ast' (b':bool) os,
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <(st, ast, b, ds)> =[ ultimate_slh c ]=> <(st', ast', b', os)> ->
  st' "b" = (if b' then 1 else 0).

Lemma ultimate_slh_flag : forall c ds,
  ultimate_slh_flag_prop c ds.
Admitted.

Definition ultimate_slh_bcc_prop (c: com) (ds :dirs) :Prop :=
  forall st ast (b: bool) st' ast' b' os,
    nonempty_arrs ast ->
    unused "b" c ->
    st "b" = (if b then 1 else 0) ->
    <(st, ast, b, ds)> =[ ultimate_slh c ]=> <(st', ast', b', os)> ->
    |-i <(st, ast, b, ds)> =[ c ]=> <("b" !-> st "b"; st', ast', b', os)>.

Lemma ultimate_slh_bcc : forall c ds,
  ultimate_slh_bcc_prop c ds.
Proof.
  apply prog_size_ind. unfold ultimate_slh_bcc_prop.
  intros c ds IH st ast b st' ast' b' os Hast Hunused Hstb Heval.
  destruct c; simpl in *; inversion Heval; subst; clear Heval.
  - (* Skip *)
    rewrite t_update_same. apply Ideal_Skip.
  - (* Asgn *) 
    rewrite t_update_permute; [| tauto].
    rewrite t_update_same.
    constructor. reflexivity.
  - (* Seq *) 
    eapply Ideal_Seq.
    + apply IH in H1; try tauto.
      * eassumption.
      * prog_size_auto.
    + apply ultimate_slh_flag in H1 as Hstb'0; try tauto.
      apply IH in H10; try tauto.
      * eapply ideal_unused_update_rev; try tauto.
      * prog_size_auto.
      * eapply spec_eval_preserves_nonempty_arrs in H1; auto. 
  (* IF *)
  - (* non-speculative *)
    simpl in H10. destruct (st "b" =? 0)%nat eqn:Eqstb; 
    destruct (beval st be) eqn:Eqbe; inversion H10; inversion H1; subst;
    clear H10; clear H1; simpl in *; rewrite Eqstb in *; rewrite Eqbe in *;
    eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit;
    rewrite t_update_same in H11; simpl in *.
    + (* true; true *)  
      apply IH in H11; try tauto.
      * replace (OBranch true) with (OBranch (negb b'0 && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        apply Ideal_If. rewrite Eqbe, Hbit; simpl.
        rewrite app_nil_r. subst. apply H11.
      * prog_size_auto.
    + (* true; false *)
      apply IH in H11; try tauto.
      * replace (OBranch false) with (OBranch (negb b'0 && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        apply Ideal_If. rewrite Eqbe, Hbit; simpl.
        rewrite app_nil_r. subst. apply H11.
      *  prog_size_auto.
    + (* false; true *)
      apply IH in H11; try tauto.
      * replace (OBranch false) with (OBranch (negb b'0 && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        apply Ideal_If. rewrite Eqbe, Hbit; simpl.
        rewrite app_nil_r. subst. apply H11.
      *  prog_size_auto.
    + apply IH in H11; try tauto.
      * replace (OBranch false) with (OBranch (negb b'0 && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        apply Ideal_If. rewrite Eqbe, Hbit; simpl.
        rewrite app_nil_r. subst. apply H11.
      *  prog_size_auto.
  - (* speculative *)
    simpl in H10. destruct (st "b" =? 0)%nat eqn:Eqstb; 
    destruct (beval st be) eqn:Eqbe; inversion H10; inversion H1; subst;
    clear H10; clear H1; simpl in *; rewrite Eqstb in *; rewrite Eqbe in *;
    eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit;
    simpl in *.
    + (* true; true *)  
      apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
        replace (OBranch true) with (OBranch (negb b && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        apply Ideal_If_F. rewrite Eqbe, Hbit; simpl.
        rewrite app_nil_r. apply H11.
      * prog_size_auto.
    + (* true; false *)  
      apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
        replace (OBranch false) with (OBranch (negb b && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        apply Ideal_If_F. rewrite Eqbe, Hbit; simpl.
        rewrite app_nil_r. apply H11.
      * prog_size_auto.
    + (* false; true *)  
      apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
        replace (OBranch false) with (OBranch (negb b && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        apply Ideal_If_F. rewrite Eqbe, Hbit; simpl.
        rewrite app_nil_r. apply H11.
      * prog_size_auto.
    + (* false; false *)
      apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
        replace (OBranch false) with (OBranch (negb b && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        apply Ideal_If_F. rewrite Eqbe, Hbit; simpl.
        rewrite app_nil_r. apply H11.
      * prog_size_auto.
  - (* While *) admit.
  - (* ARead *)
    simpl in H11. destruct (st "b" =? 1)%nat eqn:Eqstb;
    eapply flag_one_check_spec_bit in Hstb as Hbit; eauto; simpl in *;
    rewrite Eqstb in *.
    + rewrite t_update_permute; [| tauto]. rewrite t_update_same.
      apply Ideal_ARead; auto. rewrite Hbit. reflexivity.
    + rewrite t_update_permute; [| tauto]. rewrite t_update_same.
      apply Ideal_ARead; auto. rewrite Hbit. reflexivity.
  - (* ARead; contradiction *) simpl in H11. rewrite Hstb in H11; simpl in H11.
    specialize (Hast a). apply lt_neq in Hast. apply le_0_r in H11.
    exfalso; auto.
  - (* AWrite *)
    simpl in H12. destruct (st' "b" =? 1)%nat eqn:Eqstb;
    eapply flag_one_check_spec_bit in Hstb as Hbit; eauto; simpl in *;
    rewrite Eqstb in *.
    + rewrite t_update_same. apply Ideal_Write; auto.
      rewrite Hbit. reflexivity.
    + rewrite t_update_same. apply Ideal_Write; auto.
      rewrite Hbit. reflexivity.
  - (* AWrite; contradiction *) simpl in H12. rewrite Hstb in H12; simpl in H12.
    specialize (Hast a). apply lt_neq in Hast. apply le_0_r in H12.
    exfalso; auto.
Admitted.

Theorem ultimate_slh_relative_secure :
  forall c st1 st2,
    (* some extra assumptions needed by slh_bcc *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    relative_secure ultimate_slh c st1 st2.
Admitted. (* from relative noninterference + bcc *)
