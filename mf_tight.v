(* This file contains basic definitions and Lemmas about multi-valued functions *)
From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp mf_prop.
Require Import CRelationClasses Morphisms ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition tight S T (g f: S ->> T) :=
	(dom g) \is_subset_of (dom f)
	/\
	forall s, s \from_dom g -> (f s) \is_subset_of (g s).
Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
Notation "g '\tightens' f" := (tight f g) (at level 2).

Lemma tight_char S T (f g: S ->> T):
	f \tightens g <-> forall s, s \from_dom g -> s \from_dom f /\ forall t, f s t -> g s t.
Proof.
split => [[dom val] s sfd | tight]; first by split; [apply dom | apply val].
split => s sfd; first by have []:= tight s.
by move => t fst; have[_ prp]:= tight s sfd; apply prp.
Qed.

Global Instance tight_prpr S T:
	Proper ((@equiv S T) ==> (@equiv S T) ==> iff) (@tight S T).
Proof.
move => f f' eqf g g' eqg; rewrite !tight_char.
split => tight s sfd; split => [ | t gst].
			by rewrite -eqg; have [ | fd prp]:= tight s; first by rewrite eqf.
		by have [ | fd prp]:= tight s; [rewrite eqf| rewrite -(eqf s t); apply prp; rewrite (eqg s t)].
	by rewrite eqg; have [ | fd prp]:= tight s; first by rewrite -eqf.
by have [ | fd prp]:= tight s; [rewrite -eqf| rewrite (eqf s t); apply prp; rewrite -(eqg s t)].
Qed.

Section tight.
Context (S T: Type).

Lemma tight_equiv (f g: S ->> T): f \tightens g -> g \tightens f -> f =~= g.
Proof.
move => [dm val] [dm' val'] s t.
split => [fst | gst].
	by apply /val; first by apply /dm'; exists t.
by apply /val'; first by apply /dm; exists t.
Qed.

(* A thightening is a generalization of an extension of a single-valued function
to multivalued functions. It reduces to the usual notion of extension for single valued
functions: A single valued function g tightens a single valued function f if and only
if "forall s, (exists t, f(s) = t) -> g(s) = f(s)". This formula can also be written as
"forall s t, f(s) = t -> g(s) = t" and the equivalence is proven in the next lemmas.*)
Definition exte S T (g f: S ->> T) := forall s, (f s) \is_subset_of (g s).
Notation "g '\extends' f" := (exte g f) (at level 50).

Lemma exte_char (g f: S ->> T):
	g \extends f <-> forall s t, f s t -> g s t.
Proof. done. Qed.

Lemma exte_restr (f: S ->> T) P Q: P \is_subset_of Q -> f|_Q \extends f|_P.
Proof.
rewrite exte_char.
move => subs s t [Ps fst].
by split => //; apply subs.
Qed.

(* tight is almost an equivalence relation, it only fails to be symmetric *)
Global Instance tight_ref: Reflexive (@tight S T).
Proof. by move => f; rewrite !tight_char. Qed.

Global Instance tight_trans:
	Transitive (@tight S T).
Proof.
move => f g h.
move => [dm' val'] [dm val].
split => [ | s sfd]; first exact /(subs_trans dm' dm).
have hsf := val s (dm' s sfd).
exact/(subs_trans hsf (val' s sfd)).
Qed.

Lemma sing_tight_exte (f: S ->> T) g:
	f \is_singlevalued -> g \tightens f -> g \extends f.
Proof.
move => fsing [dm val] s t fst.
have [ | t' gst']:= dm s; first by exists t.
rewrite (fsing s t t') //.
by apply val => //; exists t.
Qed.

Lemma exte_dom (f g: S ->> T):
	g \extends f -> (dom f) \is_subset_of (dom g).
Proof. by move => exte s [t fst]; exists t; apply exte. Qed.

Lemma sing_exte_tight (f: S ->> T) g:
	g \is_singlevalued -> g \extends f -> g \tightens f.
Proof.
move => gsing exte.
split => s [t]; first by exists t; apply exte.
move => fst t' gst'; have gst := exte s t fst.
by rewrite (gsing s t' t).
Qed.

Lemma exte_tight (f: S ->> T) g:
	f \is_singlevalued -> g \is_singlevalued -> (g \extends f <-> g \tightens f).
Proof. split; [exact: sing_exte_tight | exact: sing_tight_exte] . Qed.

Lemma exte_sing (f: S ->> T) (g: S ->> T):
	f \extends g -> f \is_singlevalued -> g \is_singlevalued.
Proof. move => exte sing s t t' gst gst'; apply /sing; apply exte; [apply gst | apply gst']. Qed.

Lemma exte_comp R (f f': T ->> R) (g: S ->> T):
	f \extends f' -> (f o g) \extends (f' o g).
Proof.
move => fef s r [[t [gst ftr] prop]].
split => [ | t' gst']; first by exists t; split => //; apply fef.
specialize (prop t' gst').
have [r' f't'r']:= prop.
by exists r'; apply fef.
Qed.

Lemma tight_restr_r (f g: S ->> T) P Q:
	P \is_subset_of Q -> f \tightens (g \restricted_to Q) -> f \tightens (g \restricted_to P).
Proof.
rewrite !tight_char.
move => subs tight s [t [Ps gst]].
have [ | [t' fst' prp]]:= tight s; first by exists t; split; try apply subs.
split => [ | t'' fst'']; first by exists t'.
by split; last by apply prp.
Qed.

Lemma tight_restr_l (f g: S ->> T) P Q:
	P \is_subset_of Q -> (f \restricted_to P) \tightens g -> (f \restricted_to Q) \tightens g.
Proof.
rewrite !tight_char.
move => subs tight s [t gst].
have [ | [t' [Ps fst'] prp]]:= tight s; first by exists t.
split => [ | t'' [Qs fst'']]; first by exists t'; split; try apply subs.
by apply prp.
Qed.

Lemma tight_restr (f: S ->> T) P Q:
	P \is_subset_of Q -> (f \restricted_to Q) \tightens (f \restricted_to P).
Proof.
move => subs; apply /(tight_restr_l subs)/tight_ref.
Qed.

Lemma tight_restr_w (f: S ->> T) P: f \tightens (f \restricted_to P).
Proof. by rewrite !tight_char; move => s [t [Ps fst]]; by split; first by exists t. Qed.

Lemma tight_comp_r R (f: T ->> R) g (g': S ->> T):
	g \tightens g' -> (f o g) \tightens (f o g').
Proof.
rewrite !tight_char.
move => gtg' s [r [[t [g'st ftr]] prop]].
have sfd: s \from_dom g' by exists t.
have [t' gst']:= (gtg' s sfd).1.
have g'st': g' s t' by apply (gtg' s sfd).2.
move: (prop t' g'st') => [r' fgsr'].
split; first exists r'.
	split => [ | t'' gst'']; first by exists t'.
	by apply prop; apply (gtg' s sfd).2.
move => r'' [[t'' [gst'' ft''r'']] prop'].
split => //; by exists t''; split => //; apply (gtg' s sfd).2.
Qed.

Lemma restr_dom (f: S ->> T) P s:
s \from_dom (f \restricted_to P) <-> s \from_dom f /\ P s.
Proof. by split => [[t []] | [[t]]]; first split; try by exists t. Qed.

Lemma tight_exte_dom (f g: S ->> T):
	g \extends f -> f \tightens (g \restricted_to (dom f)).
Proof.
split => [s | s]; first by rewrite restr_dom => [[]].
by rewrite restr_dom => [[sfdf sfdg]] t fst; split; last apply H.
Qed.
End tight.

Section tight_comp.
Context (S T: Type).
Lemma tight_comp_l_codom R (f f': T ->> R) (g: S ->> T):
	f \tightens (f' \restricted_to (codom g)) -> (f o g) \tightens (f' o g).
Proof.
rewrite !tight_char.
move => ftf' s [r [[t [gst f'tr]] prop]].
have tfd: t \from_dom (f' \restricted_to (codom g)) by exists r; split => //; exists s.
have [r' ftr']:= (ftf' t tfd).1.
have f'tr': f' t r' by apply (ftf' t tfd).2.
split; first exists r'.
	split => [ | t'' gst'']; first by exists t.
	apply ftf'; have [r'' f't''r'']:= prop t'' gst''.
	by exists r''; split => //; exists s.
move => r'' [[t'' [gst'' ft''r'']] prop'].
split => //; exists t''; split => //.
apply ftf'; have [r''' f't''r'']:= prop t'' gst'' => //.
by exists r'''; split => //; exists s.
Qed.

Lemma tight_comp_l R (f f': T ->> R) (g: S ->> T):
	f \tightens f' -> (f o g) \tightens (f' o g).
Proof.
move => tight.
apply tight_comp_l_codom.
by apply /tight_trans; first apply /tight_restr_w.
Qed.

Lemma cotot_tight_comp_l R (f f': T ->> R) (g: S ->> T):
	g \is_singlevalued -> dom f' \is_subset_of codom g -> (f o g) \tightens (f' o g) -> f \tightens f'.
Proof.
move => sing subs [dm val].
split.
	move => t [r ftr].
	have [ | s [_ gst]]:= subs t; first by exists r.
	have sfd: s \from_dom (f' o g) by rewrite sing_rcomp => //; exists r; exists t.
	have [r' [[t' [gst' ft'r']] _]]:= dm s sfd.
	by rewrite (sing s t t') =>//; exists r'.
move => t [r' f'tr'] r ftr.
have [ | s [_ gst]]:= subs t; first by exists r'.
have sfd: s \from_dom (f' o g) by rewrite sing_rcomp => //; exists r'; exists t.
have subs':= val s sfd.
have fgsr: f o g s r by rewrite sing_rcomp => //; exists t.
have [[t' [gst' f't'r]]]:= subs' r fgsr.
by rewrite (sing s t t').
Qed.

Lemma tight_comp_inv R (f: S ->> T) (g: R ->> T) (h: S ->> R):
	h \is_surjective_partial_function -> g \is_singlevalued ->
		f \tightens (g o h) <-> (f o (mf_inv h)) \tightens g.
Proof.
rewrite !tight_char.
move => [sing /cotot_spec cotot] gsing; split.
	move => tight r [t grt].
	have prp: forall s, h s r -> exists t' r', f s t' /\ h s r' /\ g r' t'.
		move => s hsr; have [ | [t' fst'] prp]:= tight s.
			exists t; split => [ | r' hsr']; first by exists r.
			by rewrite (sing s r' r) => //; exists t.
			exists t'; have [ | [r' [hsr' gr't']] dom]:= prp t' => //.
			by exists r'.
	split; first exists t.
		split => [ |  s hrs]; first have [s hrs]:= cotot r; [exists s | exists t];
		have [t' [r' [fst' [hsr' gr't']]]]:= prp s hrs;
		rewrite (sing s r' r) in gr't' => //;
		by rewrite (gsing r t t').
	move => t' [[s [hsr fst']] _].
	have [ | _ prp']:= tight s.
		exists t.
		split; first by exists r.
		move => r' hsr'.
		rewrite (sing s r' r) => //.
		by exists t.
	have [ | [r' [hsr' gr't']] dom']:= prp' t' => //.
	have ghst': g o h s t' by split; first by exists r'.
	have ghst: g o h s t.
		split; first by exists r.
		move => r'' hsr''.
		rewrite (sing s r'' r) => //.
		by exists t.
	have cmp_sing: g o h \is_singlevalued by apply comp_sing.
	by rewrite (cmp_sing s t' t).
move => tight s [t [[r [hsr grt]]] subs].
split.
	exists t.
	have [ | [_ [_ cnd] prp]]:= tight r; first by exists t.
	have [t' fst']:= cnd s hsr.
	rewrite (gsing r t t') => //.
	by apply prp; split; first exists s.
move => t' fst'.
split => //.
exists r; split => //.
have [ | _ prp]:= tight r; first by exists t.
apply prp.
split; first by exists s.
move => s' hs'r.
have [ | [t'' [[s'']]fht''r prp'] _]:= tight r; first by exists t.
by have := prp' s' hs'r.
Qed.

Definition icf S T (f: S ->> T) g := forall s t, f s t -> f s (g s).
Notation "g '\is_choice_for' f" := (icf f g) (at level 2).
(* A more comprehensible way to state icf would be "forall s, s \from_dom f -> f s (g s)"
or "forall s, (exists t, f s t) -> f s (g s)" but avoiding the existential quatification
makes the above more convenient to use. *)

Lemma id_icf_mfinv (f: S ->> T): id \is_choice_for ((mf_inv f) o f).
Proof. by move => s s' [[t [fst _]] _]; split; [exists t | exists s]. Qed.

Lemma sing_tot_F2MF_icf (f: S ->> T) g:
	f \is_singlevalued -> f \is_total -> (g \is_choice_for f <-> F2MF g =~= f).
Proof.
move => sing /tot_spec tot.
split => [icf s t| eq s t fst]; last by by rewrite ((eq s t).2 fst).
split => [ eq | fst ]; last by rewrite (sing s t (g s)); last by apply (icf s t fst).
by have [t' fst']:= (tot s); by rewrite -eq; apply (icf s t').
Qed.

Lemma icf_comp R f' (f: T ->> R) g' (g: S ->> T):
	f' \is_choice_for f -> g' \is_choice_for g
		-> (fun s => f' (g' s)) \is_choice_for (f o g).
Proof.
move => icff icfg s r [[t [gst ftr]] prop].
split => [ | t' gst']; last exact (prop t' gst'); exists (g' s).
have gsg's: g s (g' s) by apply/ (icfg s t).
have [r' fg'sr']:= (prop (g' s) gsg's).
by split; last apply/ (icff (g' s) r').
Qed.

Lemma icf_F2MF_tight (g: S -> T) f:
	g \is_choice_for f <-> (F2MF g) \tightens f.
Proof.
rewrite !tight_char.
split => [ icf s [] t fst | tight s t fst].
	by split => [ | gs eq ]; [exists (g s) | rewrite -eq; apply: (icf s t)].
have ex: s \from_dom f by exists t.
by apply ((tight s ex).2 (g s)).
Qed.

Lemma tight_icf (g f: S ->> T):
	g \tightens f -> forall h, (h \is_choice_for g -> h \is_choice_for f).
Proof.
move => tight h icf.
apply/ icf_F2MF_tight.
apply/ tight_trans; first by apply tight.
by apply/ icf_F2MF_tight.
Qed.

Lemma exists_choice (f: S ->> T) (t: T):
	exists F, F \is_choice_for f.
Proof.
set R := make_mf (fun s t => forall t', f s t' -> f s t).
have [s | F tot]:= choice (mf.value R); last by exists F => s; apply /tot.
case: (classic (s \from_dom f)) => [[] t' fst | false]; first by exists t'.
by exists t => t' fst'; exfalso; apply false; exists t'.
Qed.

Lemma F2MF_sing_tot (f: S ->> T) (t: T):
	f \is_singlevalued /\ f \is_total <-> exists g, (F2MF g) =~= f.
Proof.
split => [ [sing tot] | [g eq] ].
	have [g icf]:= exists_choice f t.
	exists g; by apply/ sing_tot_F2MF_icf.
by split; rewrite -eq; [apply F2MF_sing | apply F2MF_tot].
Qed.

Lemma icf_tight (g f: S ->> T): (forall s, exists t', ~ f s t')
	-> (forall h, (h \is_choice_for g -> h \is_choice_for f)) -> (g \tightens f).
Proof.
rewrite !tight_char.
move => ex prop s [t fst].
split => [ | t' gst'].
	have [t' nfst']:= (ex s).
	pose g' := make_mf (fun x y => (x <> s -> g x y) /\ (x = s -> y = t')).
	have [h icf'] := (exists_choice g' t).
	apply NNPP => nex.
	have ngst': ~g s t' by move => gst'; apply nex; exists t'.
	have icf: h \is_choice_for g.
		move => s' t'' gs't''.
		case (classic (s' = s)) => [eq | neq].
			by exfalso; apply nex; exists t''; rewrite -eq.
		have g's't'': g' s' t'' by split => // eq; exfalso; apply neq.
		exact: ((icf' s' t'' g's't'').1 neq).
	suffices eq: h s = t' by apply nfst'; rewrite -eq; apply: (prop h icf s t).
	have g'st': g' s t' by trivial.
	by apply (icf' s t' g'st').2.
pose g' := make_mf (fun x y => g x y /\ (x = s -> y = t')).
have gtg: g' \tightens g.
	rewrite !tight_char.
	move => x xfd.
	split => [ | y g'xy]; last by apply g'xy.1.
	case (classic (x = s)) => [ eq | neq ]; first by exists t'; rewrite eq.
	by have [y gxy]:= xfd; exists y; by split.
have [h icf']:= (exists_choice g' t).
have icf: h \is_choice_for g.
	apply icf_F2MF_tight.
	apply/ tight_trans; first by apply/ gtg.
	by apply icf_F2MF_tight; apply icf'.
suffices val: h s = t' by rewrite -val; apply/ (prop h icf s t).
have val': g s t' /\ (s = s -> t' = t') by split.
by apply: (icf' s t' val').2.
Qed.
End tight_comp.

Global Instance icf_prpr S T: Proper (@equiv S T ==> eq ==> iff) (@icf S T).
Proof. by move => f g feg f' g' f'eg'; rewrite !icf_F2MF_tight feg f'eg'. Qed.

Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
Notation "g '\tightens' f" := (tight f g) (at level 2).
Notation "g '\extends' f" := (exte g f) (at level 50).
Notation "g '\is_choice_for' f" := (icf f g) (at level 2).

Lemma tight_comp S T R (f f': T ->> R) (g g': S ->> T):
	f \tightens f' -> g \tightens g' -> (f o g) \tightens (f' o g').
Proof.
intros; apply/tight_trans/tight_comp_l; last by apply H.
apply/tight_trans/tight_comp_r; last by apply H0.
exact/tight_ref.
Qed.

Lemma tight_comp_codom S T R (f f': T ->> R) (g g': S ->> T):
	f \tightens (f' \restricted_to (codom g')) -> g \tightens g' -> (f o g) \tightens (f' o g').
Proof.
move => tight tight'.
apply/tight_trans; first by apply /tight_comp_l_codom/tight.
by apply/tight_trans/tight_comp_r; [apply/tight_ref | apply tight'].
Qed.

Lemma tight_inv_comp S T R (f: S ->> T) (g: R ->> T) (h: S ->> R):
	(f o (h\^-1)) \tightens g -> f \tightens (g o h).
Proof.
move => tight; rewrite -(comp_id_r f).
apply /tight_trans; last by apply /tight_comp_r/icf_F2MF_tight/(@id_icf_mfinv S R h).
by rewrite -comp_assoc; apply tight_comp_l.
Qed.

Lemma tot_subs_dom S T R (f: S ->> T) (g: S ->> T) (h: T ->> R):
	codom g \is_subset_of dom h-> dom (h o g) \is_subset_of dom (h o f) -> dom g \is_subset_of dom f.
Proof.
move => tot dm s [t gst].
have [ | r [[t' []]]]:= dm s; last by exists t'.
have [ | r htr] //:= tot t; first by exists s.
by exists r; split => [ | t' gst']; [exists t | apply tot; exists s].
Qed.