From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_rcmp mf_comp mf_prop mf_tight.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section products.
Context (S T S' T': Type).
(* A modification of the following construction is used to define the product of represented spaces. *)

Definition mf_fprd S T S' T' (f : S ->> T) (g : S' ->> T') :=
	make_mf (fun s => (f s.1) \x (g s.2)).
Notation "f '**' g" := (mf_fprd f g) (at level 50).

Global Instance fprd_prpr S T S' T':
Proper ((@equiv S T) ==> (@equiv S' T') ==> (@equiv (S * S') (T * T'))) (@mf_fprd S T S' T').
Proof.
move => f f' eq g g' eq' r t.
by rewrite /mf_fprd /= eq eq'.
Qed.

Definition fprd S T S' T' (f: S -> T) (g: S' -> T') := fun p => (f p.1, g p.2).
Notation "f **_f g" := (fprd f g) (at level 50).

Lemma F2MF_fprd (f: S -> T) (g: S' -> T'): F2MF (f **_f g) =~= (F2MF f) ** (F2MF g).
Proof. by move => s [t1 t2]; rewrite /fprd/=; split; move => [-> ->]. Qed.

Definition fprd_p1 (fg: (S * S') ->> (T * T')) :=
	make_mf (fun s t => exists s' p, fg (s,s') p /\ p.1 = t).

Definition fprd_p2 (fg: (S * S') ->> (T * T')) :=
	make_mf (fun s' t' => exists s p, fg (s, s') p /\ p.2 = t').

Lemma fprd_proj1 (f: S ->> T) (g: S' ->> T'):
	(exists s', s' \from dom g) -> fprd_p1 (f ** g) =~= f.
Proof.
move => [s' [t' gs't']].
by split => [[k [p [[/= eq _] eq']]] | ]; [rewrite -eq' | exists s'; exists (s0, t')].
Qed.

Lemma fprd_proj2 (f: S ->> T) (g: S' ->> T'):
	(exists s, s \from dom f) -> fprd_p2 (f ** g) =~= g.
Proof.
move => [s [somet fst]].
move => s' t.
by split => [[k [p [[/= _ eq] eq']]] | ]; [rewrite -eq' | exists s; exists (somet, t)].
Qed.

Lemma fprd_dom R Q R' Q' (f: R ->> Q) (g: R' ->> Q'):
  dom (f ** g) === (dom f) \x (dom g).
Proof.
split; last by move => [[s' fs's] [t' ft't]]; exists (s',t').
by move => [] x [] /= fsx gty; split; [exists x.1| exists x.2].
Qed.

Lemma fprd_inv (f: S ->> T) (g: S' ->> T'): (f ** g)\^-1 =~= f\^-1 ** g\^-1.
Proof. done. Qed.

Lemma fprd_codom (f: S ->> T) (g: S' ->> T'): codom (f ** g) === (codom f) \x (codom g).
Proof. by rewrite !codom_dom_inv fprd_inv -fprd_dom. Qed.

Lemma fprd_sing (f: S ->> T) (g: S' ->> T'):
  f \is_singlevalued -> g \is_singlevalued -> (f ** g) \is_singlevalued.
Proof.
move => fsing gsing [s1 s2] [t1 t2] [t'1 t'2] [fst gst] [fst' gst'].
by rewrite (fsing s1 t1 t'1) // (gsing s2 t2 t'2).
Qed.

Lemma fprd_tot (f: S ->> T) (g: S' ->> T'):
	f \is_total -> g \is_total -> (f ** g) \is_total.
Proof. by rewrite !tot_spec fprd_dom => -> ->. Qed.

Lemma tot_fprd (f: S ->> T) (g: S' ->> T') (s: S) (s': S'):
	(f ** g) \is_total -> f \is_total /\ g \is_total.
Proof.
move => tot; have [[t t' [/= fst gs't']] ]:= tot (s, s').
move/tot_spec: tot; rewrite fprd_dom => eq.
by rewrite !tot_spec; apply/ (sprd_All_inv _ _ eq); [exists t; apply fst | exists t'; apply gs't'].
Qed.

Lemma fprd_cotot (f: S ->> T) (g: S' ->> T'):
	f \is_cototal -> g \is_cototal -> (f ** g) \is_cototal.
Proof. by rewrite !cotot_spec fprd_codom => -> ->. Qed.

Lemma fprd_rcmp R R' (f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
	(f ** g) o_R (f' ** g') =~= (f o_R f') ** (g o_R g').
Proof.
by split => [[[r s'] [[f'st g's't] []]] | [[r [f'rs fst]] [s' []]]]; [split; [exists r | exists s'] | exists (r, s')].
Qed.

Lemma fprd_comp R R' (f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
	(f ** g) o (f' ** g') =~= (f o f') ** (g o g').
Proof.
move => r t.
split => [[/fprd_rcmp [rcmpf rcmpg]] | [[rcmp subs] [rcmp' subs']]].
	rewrite fprd_dom => subs; split; split => // s frs.
		by have [s' [grs g'st]]:= rcmpg; have []//:= subs (s, s').
	by have [s' [grs g'st]]:= rcmpf; have []//:= subs (s', s).
split; first exact/fprd_rcmp.
by rewrite fprd_dom => s []; split; [apply subs | apply subs'].
Qed.

Lemma fprd_tight (f: S ->> T) (g: S' ->> T') (f': S ->> T) (g': S' ->> T'):
	f \tightens f' -> g \tightens g' -> (mf_fprd f g) \tightens (mf_fprd f' g').
Proof.
move => tight tight'; apply split_tight => [ | s dm t [fst gst]].
	by rewrite !fprd_dom => s [dm dm']; split; apply/tight_dom; try apply/dm; try apply/dm'.
by move/fprd_dom: dm => [dm dm']; split; apply/tight_val; try apply /fst; try apply /gst.
Qed.

End products.
Notation "f '**' g" := (mf_fprd f g) (at level 50).
Notation "f '**_f' g" := (fprd f g) (at level 50).