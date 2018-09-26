From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp mf_prop mf_tight.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section products.
Context (S T S' T': Type).
(* A modification of the following construction is used to define the product of represented spaces. *)

Definition mf_fprd S T S' T' (f : S ->> T) (g : S' ->> T') :=
	make_mf (fun c x => f c.1 x.1 /\ g c.2 x.2).
Notation "f '**' g" := (mf_fprd f g) (at level 50).

Global Instance fprd_prpr S T S' T':
Proper ((@equiv S T) ==> (@equiv S' T') ==> (@equiv (S * S') (T * T'))) (@mf_fprd S T S' T').
Proof.
move => f f' eq g g' eq' r t.
by rewrite /mf_fprd /= eq eq'.
Qed.

Lemma mfpp_tight (f: S ->> T) (g: S' ->> T') (f': S ->> T) (g': S' ->> T'):
	f \tightens f' -> g \tightens g' -> (mf_fprd f g) \tightens (mf_fprd f' g').
Proof.
rewrite !tight_char.
move => tigh tigh' [s s'] [[t t'] [/=f'st fs't']].
have sfd: s \from_dom f' by exists t.
have [[r fsr] prop] := tigh s sfd.
have s'fd: s' \from_dom g' by exists t'.
have [[r' gsr'] prop'] := tigh' s' s'fd.
split; first by exists (r, r').
move => [q q'] [/= fsq gs'q'].
by split; [apply prop | apply prop'].
Qed.

Definition fprd S T S' T' (f: S -> T) (g: S' -> T') := fun p => (f p.1, g p.2).
Notation "f **_f g" := (fprd f g) (at level 50).

Lemma F2MF_fprd Q Q' A A' (f: Q -> A) (g: Q' -> A'):
	F2MF (f **_f g) =~= (F2MF f) ** (F2MF g).
Proof.
split; rewrite /F2MF /=; first by move <-.
by rewrite /fprd/mf_fprd => [[-> ->]]; rewrite -surjective_pairing.
Qed.

Definition ppp1 (fg: (S * S') ->> (T * T')) :=
	make_mf (fun s t => exists s' p, fg (s,s') p /\ p.1 = t).

Definition ppp2 (fg: (S * S') ->> (T * T')) :=
	make_mf (fun s' t' => exists s p, fg (s, s') p /\ p.2 = t').

Lemma ppp1_proj (f: S ->> T) (g: S' ->> T'):
	(exists s', s' \from_dom g) -> ppp1 (f ** g) =~= f.
Proof.
move => [s' [t' gs't']].
by split => [[k [p [[/= eq _] eq']]] | ]; [rewrite -eq' | exists s'; exists (s0, t')].
Qed.

Lemma ppp2_proj (f: S ->> T) (g: S' ->> T'):
	(exists s, s \from_dom f) -> ppp2 (f ** g) =~= g.
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

Lemma fprd_inv (f: S ->> T) (g: S' ->> T'):
	(f ** g)\^-1 =~= f\^-1 ** g\^-1.
Proof. done. Qed.

Lemma fprd_codom (f: S ->> T) (g: S' ->> T'):
  codom (f ** g) === (codom f) \x (codom g).
Proof. by rewrite !codom_dom_inv fprd_inv -fprd_dom. Qed.

Lemma fprd_cotot (f: S ->> T) (g: S' ->> T'):
	f \is_cototal -> g \is_cototal -> (f ** g) \is_cototal.
Proof.
rewrite !cotot_spec.
move => cot cot' [t t'].
have [s fst]:= cot t.
have [s' gs't']:= cot' t'.
by exists (s, s').
Qed.

Lemma fprd_comp R R' (f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
	(f ** g) o (f' ** g') =~= (f o f') ** (g o g').
Proof.
split => [[] [] fgx [] [] | [] [] [] s1 []]; last first.
	move => fxs1 fs1ffggx H [] [] s2 [] fxs2 fs2ffggx H'.
	split => [ | [] s'1 s'2 [] fs' gs']; first by exists (s1,s2).
	by move: (H s'1 fs') (H' s'2 gs') => [] t' fst [] t'' ; exists (t',t'').
move => fxfgx gxfgx [] ffgxffggx gfgxffggx H.
split; split => [ | s' f'xs]; [by exists fgx.1 | | by exists fgx.2 | ].
	have temp: ((s', fgx.2) \from_dom (f ** g)) by apply: ((H (s', fgx.2))).
	by move: temp => [] [] x1 x2 [] /= fsx1; exists x1.
have temp: ((fgx.1,s') \from_dom (f ** g)) by apply: ((H (fgx.1, s'))).
by move: temp => [] [] x1 x2 [] /= fsx1; exists x2.
Qed.

Lemma fprd_sing (f: S ->> T) (g: S' ->> T'):
  f \is_singlevalued /\ g \is_singlevalued -> (f ** g) \is_singlevalued.
Proof.
move => [fsing gsing] s t t' [] fst gst [] fst' gst'.
by apply: injective_projections; [apply (fsing s.1)| apply (gsing s.2)].
Qed.

Lemma fprd_tot (f: S ->> T) (g: S' ->> T'):
	f \is_total /\ g \is_total -> (f ** g) \is_total.
Proof.
by rewrite fprd_dom; case => -> ->.
Qed.

Lemma tot_fprd (f: S ->> T) (g: S' ->> T') (s: S) (s': S'):
	(f ** g) \is_total -> f \is_total /\ g \is_total.
Proof.
move => /tot_spec tot; have [[t t' [/= fst gs't']] ]:= tot (s, s').
move/tot_spec: tot; rewrite fprd_dom => tot.
by apply/ (sprd_All_inv _ _ tot); [exists t; apply fst | exists t'; apply gs't'].
Qed.
End products.
Notation "f '**' g" := (mf_fprd f g) (at level 50).
Notation "f '**_f' g" := (fprd f g) (at level 50).