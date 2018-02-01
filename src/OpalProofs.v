Require Import Opal.OpalSemantics CpdtTactics.

Definition omega_reps (omega: omega_t) (Omega: Omega_t) : Prop :=
  forall k, Omega_in Omega k -> (exists v, WorldVarMap.MapsTo k v omega).

Definition sigma_reps (sigma: sigma_t) (Sigma: Sigma_t) : Prop :=
  forall n v, Sigma_in Sigma n v ->
              exists val, sigma_get sigma n v = Some val.

Theorem sexp_progress:
  forall s omega sigma Omega Pi Sigma,
    well_formed_sexp s Omega Pi Sigma ->
    omega_reps omega Omega ->
    sigma_reps sigma Sigma ->
    (exists sv, eval_sexp s sigma omega Pi = Some sv).
Proof.
  induction s ; intros ; inversion H ; subst.
  * unfold eval_sexp. eauto.
  * assert (pi_mem n Pi = true).
    unfold Pi_in in H8. unfold pi_mem.
    eapply NodeMap.mem_1.
    unfold NodeMap.In. exists tt. auto.
    unfold sigma_reps in H1.
    specialize (H1 n v H8).
    inversion H1.
    exists x.
    unfold eval_sexp.
    rewrite H2.
    apply H3.
  * assert (pi_mem n Pi = true).
    eapply NodeMap.mem_1.
    unfold NodeMap.In. exists tt. auto.

    unfold eval_sexp.
    unfold omega_reps in H0.
    specialize (H0 w).
    intuition.
    destruct H3.
    specialize (WorldVarMap.find_1 H0).
    intros.
    unfold omega_get.
    rewrite H3.

    unfold sigma_reps in H1.
    specialize (H1 n v).
    intuition.
    destruct H4.
    exists x0.
    eauto.

    unfold omega_reps in H0.
    specialize (H0 w).
    intuition.
    unfold omega_get.
    inversion H3.
    specialize (WorldVarMap.find_1 H0).
    edestruct WorldVarMap.find ; intros ; try discriminate.
    injection H4 ; clear H4.
    intros. subst.
    unfold eval_sexp.
    destruct H3.
    unfold omega_get.
    specialize (WorldVarMap.find_1 H0). intros. rewrite H4.
    destruct (sigma_get x n v) eqn:? ; eauto.
  * specialize (IHs1 omega sigma Omega Sigma Pi).
    specialize (IHs2 omega sigma Omega Sigma Pi).
    intuition.
    inversion H2. inversion H3.
    unfold eval_sexp.
    fold eval_sexp.
    edestruct eval_sexp; edestruct eval_sexp; eauto.
Qed.

Theorem bool_progress:
  forall b omega sigma Omega Sigma Pi,
    well_formed_bool b Omega Sigma Pi ->
    omega_reps omega Omega ->
    sigmas_reps sigma Sigma ->
    (exists bv, eval_bool b sigma omega Pi = Some bv).
Proof.
  induction b ; intros ; inversion H ; subst.
  * unfold eval_bool. eauto.
  * unfold eval_bool. eauto.
  * specialize (IHb1 omega sigma Omega Sigma Pi H4 H0 H1).
    specialize (IHb2 omega sigma Omega Sigma Pi H8 H0 H1).
    crush.
    destruct x0 ; eauto.
  * specialize (IHb1 omega sigma Omega Sigma Pi H4 H0 H1).
    specialize (IHb2 omega sigma Omega Sigma Pi H8 H0 H1).
    crush.
    destruct x0 ; eauto.
  * specialize (sexp_progress) as sp1.
    specialize (sexp_progress) as sp2.
    specialize (sp1 s omega sigma Omega Sigma Pi H4 H0 H1).
    specialize (sp2 s0 omega sigma Omega Sigma Pi H8 H0 H1).
    crush.
    eauto.
  * specialize (sexp_progress) as sp1.
    specialize (sexp_progress) as sp2.
    specialize (sp1 s omega sigma Omega Sigma Pi H4 H0 H1).
    specialize (sp2 s0 omega sigma Omega Sigma Pi H8 H0 H1).
    crush.
    eauto.
Qed.


Theorem progress:
  forall c sigmas Sigma omega Omega Pi eta Eta mu rho,
    sigmas <> nil ->
    omega_reps omega Omega ->
    sigmas_reps sigmas Sigma ->
    eta_reps eta Eta ->
    mu_reps mu Sigma ->
    (exists Omega', well_formed_com c Omega Sigma Pi Eta Omega') ->
    exists sigma' omega',
      eval_com c sigmas omega Pi rho eta mu = Some (sigma', omega').
Proof.
  induction c ; intros ; unfold eval_com ; fold eval_com.
  * intros. destruct sigmas. contradiction H. reflexivity.
    exists s. exists omega. auto.
  * inversion H4.
    inversion H5.
  * inversion H4. inversion H5.
    subst. intuition.

    specialize (bool_progress).
    intros.

    destruct sigmas. contradiction H. reflexivity.
    specialize (H6 b omega (s::sigmas) Omega Sigma Pi H10 H0 H1).
    destruct (eval_bool b (s :: sigmas) omega Pi).
    specialize (IHc1 (s::sigmas) Sigma omega Omega Pi eta Eta mu rho).
    specialize (IHc2 (s::sigmas) Sigma omega Omega Pi eta Eta mu rho).
    destruct b0.
  - intuition.
    eapply H9.
    exists Omega'.
    auto.
  - intuition.
    eapply H7.
    exists Omega''.
    auto.
  - inversion H6. inversion H7.
    * destruct sigmas. contradiction H. reflexivity.
      specialize (IHc (s::sigmas) Sigma omega Omega (pi_add n Pi) eta Eta mu rho).
      intuition.
      assert (exists Omega' : Omega_t,
                 well_formed_com c Omega Sigma (pi_add n Pi) Eta Omega').
  - inversion H4. inversion H6. subst. exists x. apply H15.
  - crush.
    * destruct sigmas. contradiction H. reflexivity.
      specialize (IHc (s::sigmas) Sigma omega Omega Pi eta Eta mu n).
      intuition.
      assert (exists Omega' : Omega_t, well_formed_com c Omega Sigma Pi Eta Omega').
  - destruct H4. exists x. inversion H4. auto.
  - intuition.
    * destruct sigmas. contradiction H. reflexivity.
      inversion H4.
      inversion H5.
      assert (pi_mem n Pi = true). specialize (NodeSet.mem_spec Pi n). crush.
      subst.
      rewrite H26.
      remember (sigma_set s1 n v EmptySexpValue) as s2.
      pose (OpSet.add o Eta).
      pose (NodeVarSet.add (n,v) Sigma).
      specialize (IHc (s2::sigmas) (NodeVarSet.add (n, v) Sigma) omega Omega Pi (eta_set eta o n v s) t (mu_set mu n v v0 v1 v2 s0) n).
      intuition.

      assert (s2 :: sigmas = nil -> False).
      intros. discriminate.

      assert (sigmas_reps (s2 :: sigmas) (NodeVarSet.add (n, v) Sigma)).
      unfold sigmas_reps in *.
      unfold sigmas_get in *.
      unfold sigma_set in *.
      intros.
      destruct (NodeVarType.eq_dec (n,v) (n0,v3)).
  - specialize (NodeVarMap.add_1 s1 EmptySexpValue e).
    intros.
    exists (EmptySexpValue).
    specialize (NodeVarMap.find_1 H8).
    intros.
    rewrite <- Heqs2 in H9.
    assert (sigma_get s2 n0 v3 = Some EmptySexpValue).
    + crush.
    + rewrite H10. auto.
  - fold sigmas_get in *.
    specialize (H1 n0 v3).
    specialize (NodeVarSet.add_spec Sigma (n,v) (n0,v3)).
    intros.
    destruct H8.
    intuition.
    destruct (sigma_get s2 n0 v3) eqn:?.
    + exists s3. auto.
    + inversion H10.
      destruct (sigma_get s1 n0 v3) eqn:?.
      ** subst.
         unfold sigma_get in *.
         specialize (NodeVarMap.find_2 Heqo1).
         intros.
         specialize (NodeVarMap.add_2 EmptySexpValue n1 H13).
         intros.
         specialize (NodeVarMap.find_1 H14).
         intros.
         assert (sigma_get (NodeVarMap.add (n, v) EmptySexpValue s1) n0 v3 = Some s3). unfold sigma_get. auto.
         assert (sigma_get (NodeVarMap.add (n, v) EmptySexpValue s1) n0 v3 = None). unfold sigma_get. auto.
         rewrite H16 in H17. discriminate.
      ** auto.
  -
    assert (eta_reps (eta_set eta o n v s) t).
    unfold eta_reps in *.
    intros.
    unfold eta_get in *.
    unfold eta_set in *.
    destruct (OpType.eq_dec o op0).
    specialize (OpMap.add_1 eta (n,v,s) e).
    exists (n,v,s).
    specialize (OpMap.find_1 H9).
    intros.
    auto.
    subst.
    specialize H2 with op0.
    assert (OpSet.In op0 Eta).
    specialize (OpSet.add_spec Eta o op0).
    intuition.
    intuition.
    inversion H11.
    exists x0.
    specialize (OpMap.find_2 H2).
    intros.
    specialize (OpMap.add_2 (n,v,s) n0 H12).
    intros.
    specialize (OpMap.find_1 H13).
    auto.

    assert (mu_reps (mu_set mu n v v0 v1 v2 s0) (NodeVarSet.add (n, v) Sigma)).
    unfold mu_reps in *.
    unfold mu_get in *.
    unfold mu_set in *.
    intros.
    destruct (NodeVarType.eq_dec (n,v) (n0,v3)) eqn:?.
    + specialize (NodeVarMap.add_1 mu (v0, v1, v2, s0) e).
      intros.
      specialize (NodeVarMap.find_1 H10).
      intros.
      exists (v0,v1,v2,s0). auto.
    + specialize (H3 n0 v3).
      assert (NodeVarSet.In (n0, v3) Sigma).
      specialize (NodeVarSet.add_spec Sigma (n,v) (n0,v3)).
      intros.
      destruct H10. intuition.
      intuition.
      inversion H11.
      specialize (NodeVarMap.find_2 H3).
      intros.
      specialize (NodeVarMap.add_2 (v0, v1, v2, s0) n1 H13).
      intros.
      exists x0.
      specialize (NodeVarMap.find_1 H14).
      intros.
      auto.
    + assert (exists Omega', well_formed_com c Omega (NodeVarSet.add (n, v) Sigma) Pi t Omega').
      exists x. auto.

      intuition.
      * destruct sigmas. contradiction H. reflexivity.
        inversion H4.
        inversion H5.
        subst.
        unfold eta_reps in *.
        unfold eta_get in *.
        specialize (H2 o H8).
        inversion H2.
        rewrite H6.
        destruct x0, p.
        pose

          subst. intuition.
        specialize (IHc n Pi).
        eapply IHc.
        eauto.
      * inversion H. inversion H0.
        subst. intuition.
        specialize (IHc n Pi).
        assert (pi_mem n Pi = true). inversion H16.
        crush.
  - inversion H16; subst.
    +

      specialize (NodeSet.mem_spec Pi n). crush.
      assert
        inversion H16.
      crush.
      eapply IHc.
Qed.