Require Import Opal.OpalSemantics CpdtTactics.

Module OpalProofs (NodeType VarType WorldVarType: OrderedType.OrderedType).
  Include Opal NodeType VarType WorldVarType.

  Definition omega_reps (omega: omega_t) (Omega: Omega_t) : Prop :=
    forall k, Omega_in Omega k -> (exists v, WorldVarMap.MapsTo k v omega).

  Definition sigma_reps (sigma: sigma_t) (Sigma: Sigma_t) : Prop :=
    forall n v, Sigma_in Sigma n v ->
                exists val, sigma_get sigma n v = Some val.

  Theorem sexp_progress:
    forall s omega sigma Sigma Omega Pi,
      well_formed_sexp s Omega Pi Sigma ->
      omega_reps omega Omega ->
      sigma_reps sigma Sigma ->
      (exists sv, EvalSexp s sigma omega Pi sv).
  Proof.
  Admitted.

  Theorem bool_progress:
    forall b omega sigma Sigma Omega Pi,
      well_formed_bool b Omega Pi Sigma ->
      omega_reps omega Omega ->
      sigma_reps sigma Sigma ->
      (exists bv, EvalBool b sigma omega Pi bv).
  Proof.
  Admitted.

  Check well_formed_com.

  Theorem com_progress:
    forall c omega sigma rho mu Sigma Omega Pi sigma' omega' Omega',
      well_formed_com c Omega Pi Sigma Omega' ->
      omega_reps omega Omega ->
      sigma_reps sigma Sigma ->
      (exists sigma omega, EvalCom c sigma omega Pi rho mu sigma' omega').
  Proof.
  Admitted.

  Theorem commit_movement : True.
  (* Assuming no intermediate reads or writes, moving a "hyp" to its commit does not alter the state of the world *)
  (* translation to a language that stores original state and com and re-computes each time yields same final state *)
  Proof.
  Admitted.

  Theorem hyp_noninterference : True.
  (* Other than weight and commit, hyp worlds have noninterference *)
  (* Can drop uncommited fresh hyp's everywhere with no effect on final store *)
  Proof.
  Admitted.

  Theorem hyp_with_escape_power : True.
  (* No additional power granted by commiting a hyp outside of a "with"
     (since any of its reads or writes must have been permissioned at some point) *)
  (* Any change committed by a hyp must have been permissioned by a with at some point *)
  Proof.
  Admitted.
End OpalProofs.
