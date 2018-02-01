Require Import Opal.OpalSemantics CpdtTactics.

Module OpalInterp (NodeType VarType WorldVarType: OrderedType.OrderedType).
  Include Opal NodeType VarType WorldVarType.

  Fixpoint eval_eq (l r: sexp) {lp: sexp_is_value l} {rp: sexp_is_value r}
    : bool_value.
    unshelve
      refine (
        match l as l', r as r'
              return l=l' -> r=r' -> bool_value
        with
        | EmptySexp, EmptySexp =>
          fun _ _ =>
            exist _ TrueBool _
        | (ConsSexp ll lr), (ConsSexp rl rr) =>
          fun _ _ =>
            let leqv := eval_eq ll rl _ _ in
            let leq := proj1_sig leqv in
            let reqv := eval_eq lr rr _ _ in
            let req := proj1_sig reqv in
            match leq as leq', req as req'
                  return leq=leq' -> req=req' -> bool_value
            with
            | TrueBool, TrueBool =>
              fun _ _ =>
                exist _ TrueBool _
            | _, _ =>
              fun _ _ =>
                exist _ FalseBool _
            end eq_refl eq_refl
        | _, _ =>
          fun _ _ =>
            exist _ FalseBool _
        end eq_refl eq_refl) ;
      auto ;
      subst ;
      inversion lp ;
      inversion rp ;
      eauto.
  Defined.

  Arguments eval_eq l r : clear implicits.

  Fixpoint eval_mem
           (l r: sexp) {lp: sexp_is_value l} {rp: sexp_is_value r}
    : bool_value.
    unshelve
      refine (
        match r as r' return r=r' -> bool_value with
        | EmptySexp => fun _ => exist _ FalseBool _
        | ConsSexp rl rr =>
          fun _ =>
            let eqv := eval_eq l rl _ _ in
            let eq := proj1_sig eqv in
            match eq as eq' return eq=eq' -> bool_value with
            | TrueBool =>
              fun _ => exist _ TrueBool _
            | FalseBool =>
              fun _ => eval_mem l rr lp _
            | _ =>
              fun _ => _
            end eq_refl
        | _ => fun _ => exist _ FalseBool _
        end eq_refl
      ) ;
      subst ;
      eauto ;
      inversion rp ;
      eauto.
  Defined.

  Arguments eval_mem l r : clear implicits.

  Fixpoint eval_sexp (s: sexp) (sigma: sigma_t) (omega: omega_t) (pi: pi_t) {struct s} : option sexp_value.
    unshelve
      refine (
        match s with
        | EmptySexp => Some (exist _ EmptySexp _)
        | VarSexp n v =>
          if pi_mem n pi then
            sigma_get sigma n v
          else
            None
        | WeightSexp w n v =>
          match omega_get omega w with
          | Some sigma_hyp =>
            sigma_get sigma_hyp n v
          | None =>
            None
          end
        | ConsSexp s1 s2 =>
          match eval_sexp s1 sigma omega pi,
                eval_sexp s2 sigma omega pi with
          | Some (exist _ s1v _), Some (exist _ s2v _) =>
            Some (exist _ (ConsSexp s1v s2v) _)
          | _, _ => None
          end
        end)
    .
    constructor.
    constructor ; auto.
  Defined.


  Fixpoint eval_bool (b: bool) (sigma: sigma_t) (omega: omega_t) (pi: pi_t) {struct b} : option bool_value.
    unshelve
      refine (
        match b with
        | TrueBool => Some (exist _ TrueBool _)
        | FalseBool => Some (exist _ FalseBool _)
        | ConjBool b1 b2 =>
          match eval_bool b1 sigma omega pi,
                eval_bool b2 sigma omega pi
          with
          | Some (exist _ TrueBool _), Some b2' => Some b2'
          | Some (exist _ FalseBool _), Some b2' => Some (exist _ FalseBool _)
          | _, _ => None
          end
        | DisjBool b1 b2 =>
          match eval_bool b1 sigma omega pi,
                eval_bool b2 sigma omega pi
          with
          | Some (exist _ FalseBool _), Some b2' => Some b2'
          | Some (exist _ TrueBool _), Some b2' => Some (exist _ TrueBool _)
          | _, _ => None
          end
        | EqBool s1 s2 =>
          match eval_sexp s1 sigma omega pi,
                eval_sexp s2 sigma omega pi
          with
          | Some (exist _ l lp), Some (exist _ r rp) => Some (eval_eq l r lp rp)
          | _, _ => None
          end
        | MemBool s1 s2 =>
          match eval_sexp s1 sigma omega pi,
                eval_sexp s2 sigma omega pi
          with
          | Some (exist _ l lp), Some (exist _ r rp) => Some (eval_mem l r lp rp)
          | _, _ => None
          end
        end)
    ;
    eauto.
  Defined.

  Fixpoint eval_com (c: com) (sigma: sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (mu: mu_t) {struct c} : option (sigma_t * omega_t).
    unshelve (
        refine (
            match c with
            | SkipCom => Some (sigma, omega)
            | SeqCom c1 c2 =>
              match eval_com c1 sigma omega pi rho mu with
              | None => None
              | Some (sigma', omega') =>
                eval_com c2 sigma' omega' pi rho mu
              end
            | IfCom b c1 c2 =>
              match eval_bool b sigma omega pi with
              | Some (exist _ TrueBool _) =>
                eval_com c1 sigma omega pi rho mu
              | Some (exist _ FalseBool _) =>
                eval_com c2 sigma omega pi rho mu
              | _ => None
              end
            | WithCom n c =>
              eval_com c sigma omega (pi_add n pi) rho mu
            | AtCom n c =>
              eval_com c sigma omega pi n mu
            | WorldAssignCom u c =>
              match eval_com c sigma omega_0 pi rho mu with
              | None => None
              | Some (sigma_hyp, omega_hyp) =>
                Some (sigma, omega_set omega u sigma_hyp)
              end
            | CommitCom w =>
              match omega_get omega w with
              | None => None
              | Some sigma_hyp =>
                let merged_sigma : NodeVarMap.t (option sexp_value) :=
                    NodeVarMap.mapi
                      (fun key sh =>
                         match key with
                         | (n, v) =>
                           match mu_get mu n v,
                                 sigma_get sigma n v
                           with
                           | Some merge_func, Some sc =>
                             Some (merge_func sc sh)
                           | _, _ => None
                           end
                         end)
                      sigma_hyp
                in
                match
                  NodeVarMap.fold
                    (fun k vo so =>
                       match vo, so with
                       | Some v, Some s =>
                         Some (NodeVarMap.add k v s)
                       | _, _ => None
                       end) merged_sigma (Some sigma)
                with
                | None => None
                | Some sigma' =>
                  Some (sigma', omega)
                end
              end
            end
          )
      ).
  Defined.
End OpalInterp.