Require Import FMapList String OrderedTypeEx CpdtTactics.

Fixpoint string_lt (l r: string) : Prop :=
  match l, r with
  | EmptyString, EmptyString => Logic.False
  | EmptyString, _ => Logic.True
  | String lh lr, String rh rr =>
    match Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii lh) (Ascii.nat_of_ascii rh) with
    | inleft (left _) => Logic.True
    | inleft (right _) => string_lt lr rr
    | inright _ => Logic.False
    end
  | _, _ => Logic.False
  end.

Module String_as_OT <: UsualOrderedType.
  Definition t := string.

  Definition eq := @eq string.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := string_lt.

  Lemma lt_trans : forall x y z : t, string_lt x y -> string_lt y z -> string_lt x z.
  Proof.
    intros x.
    induction x; intros ; destruct z; destruct y; try solve [inversion H] ; auto.
    specialize IHx with y z.
    unfold string_lt in *.
    fold string_lt in *.
    do 3 (edestruct Compare_dec.lt_eq_lt_dec ;
          try (destruct s, s0) ;
          intuition).
  Qed.

  Lemma lt_not_eq : forall x y : t, string_lt x y -> ~ eq x y.
  Proof.
    intros x.
    induction x ; destruct y; unfold not ; intros; auto.
    discriminate H0.
    unfold string_lt in *.
    fold string_lt in *.
    edestruct Compare_dec.lt_eq_lt_dec; auto.
    injection H0. intros.
    destruct s. rewrite H2 in l. intuition.
    specialize IHx with y.
    injection H0.
    intros. eapply IHx; auto.
  Qed.

  Definition compare x : forall y, OrderedType.Compare string_lt eq x y.
  Proof.
    induction x; intros.
    * destruct y.
      - assert (eq "" ""). reflexivity.
        constructor 2. auto.
      - constructor 1. unfold string_lt. auto.
    * destruct y.
      - constructor 3. unfold string_lt. auto.
      - remember (Ascii.nat_of_ascii a) as an.
        remember (Ascii.nat_of_ascii a0) as a0n.
        specialize Ascii.ascii_nat_embedding with a.
        specialize Ascii.ascii_nat_embedding with a0.
        intros.
        specialize IHx with y.
        destruct Compare_dec.lt_eq_lt_dec with an a0n ;
          try (destruct s) ;
          inversion IHx;
          [> constructor 1 ..
          | constructor 2
          | constructor 3
          | constructor 3
          | constructor 3
          | constructor 3 ] ;
          crush ;
          edestruct Compare_dec.lt_eq_lt_dec;
          intuition.
  Qed.

  Definition eq_dec := string_dec.
End String_as_OT.

Module StringPair_OT := PairOrderedType String_as_OT String_as_OT.
Module StringPairMap := FMapList.Make(StringPair_OT).