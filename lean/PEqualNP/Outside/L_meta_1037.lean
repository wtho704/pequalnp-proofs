import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1037

open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩


-- Reserve the distinct gate wires that already supply the auxiliary outputs.
-- A cut through all other gates must expose six different input wires.
theorem reserveBound {r : ℕ} (f : Fin (r+1) → (Fin 6 → Bool) → Bool)
    (a b : Fin 6 → Fin 6 → Bool)
    (hpos : ∀ i : Fin r, ∃ x, f i.castSucc x = true)
    (hproj : ∀ (i : Fin r) (p : Fin 6), ∃ x, f i.castSucc x ≠ x p)
    (hdist : ∀ i j : Fin r, i ≠ j → ∃ x, f i.castSucc x ≠ f j.castSucc x)
    (hkeep : ∀ (i : Fin r) (j : Fin 6), f i.castSucc (a j) = true → f i.castSucc (b j) = true)
    (hfall : ∀ j : Fin 6, f (Fin.last r) (a j) = true ∧ f (Fin.last r) (b j) = false)
    (hsource : ∀ (j p : Fin 6), a j p = true → b j p = false → p = j)
    (gs : List Gate) (out : Fin (r+1) → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ i x, Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = f i x) :
    r + 5 ≤ gs.length := by
  classical
  let C : Circuit := ⟨gs,0⟩
  have ev (i x) : value C x (out i) = f i x := he i x
  let W := Finset.Ico 6 (6+C.size)
  let R := Finset.univ.image (fun i : Fin r => out i.castSucc)
  let G := W \ R
  have hs : R ⊆ W := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    apply Finset.mem_Ico.mpr
    constructor
    · by_contra! h
      obtain ⟨x, hx⟩ := hproj i ⟨out i.castSucc,h⟩
      exact hx ((ev i.castSucc x).symm.trans (input_value C x ⟨out i.castSucc,h⟩))
    · by_contra! h
      obtain ⟨x, hx⟩ := hpos i
      have e := missing_value C x (out i.castSucc) h
      rw [ev, hx] at e
      contradiction
  have inj : Function.Injective (fun i : Fin r => out i.castSucc) := by
    intro i j hij
    change out i.castSucc = out j.castSucc at hij
    by_contra hne
    obtain ⟨x, hx⟩ := hdist i j hne
    apply hx
    rw [← ev i.castSucc x, ← ev j.castSucc x, hij]
  have rc : R.card = r := by simp [R, Finset.card_image_of_injective _ inj]
  have wc : W.card = C.size := by simp [W]
  have gc : G.card + r = C.size := by
    rw [← wc, ← rc]
    exact Finset.card_sdiff_add_card_eq_card hs
  have goodG (u : ℕ) (hu : u ∈ G) : 6 ≤ u ∧ u < 6+C.size :=
    Finset.mem_Ico.mp (Finset.mem_sdiff.mp hu).1
  obtain ⟨B, hd, hc, transfer⟩ := cut C hg G goodG (6+C.size) {out (Fin.last r)}
    (fun u _ hg' => (goodG u hg').2)
  have members (j : Fin 6) : j.val ∈ B := by
    by_contra hnot
    have implies (u : ℕ) (hu : u ∈ B) :
        value C (a j) u = true → value C (b j) u = true := by
      intro ha
      by_contra! hb
      have hb' := Bool.eq_false_iff.mpr hb
      by_cases lo : u < 6
      · let p : Fin 6 := ⟨u,lo⟩
        have ia : a j p = true := (input_value C (a j) p).symm.trans ha
        have ib : b j p = false := (input_value C (b j) p).symm.trans hb'
        exact hnot ((congrArg Fin.val (hsource j p ia ib)) ▸ hu)
      by_cases hi : u < 6+C.size
      · have memW : u ∈ W := Finset.mem_Ico.mpr ⟨by omega,hi⟩
        have memR : u ∈ R := by
          by_contra hn
          exact Finset.disjoint_left.mp hd hu (Finset.mem_sdiff.mpr ⟨memW,hn⟩)
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp memR
        rw [ev] at ha hb'
        exact Bool.noConfusion ((hkeep i j ha).symm.trans hb')
      · exact Bool.noConfusion (ha.symm.trans (missing_value C (a j) u (by omega)))
    have e := transfer (a j) (b j) implies (out (Fin.last r)) (Finset.mem_singleton_self _)
      ((ev (Fin.last r) _).trans (hfall j).1)
    rw [ev, (hfall j).2] at e
    contradiction
  have incl : Finset.range 6 ⊆ B := fun k hk => members ⟨k, Finset.mem_range.mp hk⟩
  have cb := Finset.card_le_card incl
  have cg := Finset.card_filter_le G (fun u => u < 6+C.size)
  simp only [Finset.card_range] at cb
  simp only [Finset.card_singleton] at hc
  change r + 5 ≤ C.size
  omega

-- Truth tables use the first input as the least significant index bit.
def twMask (j : Fin 33) : ℕ :=
  ([
    0xffaaffaaffaaffaa, 0xfffffffff0f0f0f0, 0xffffccccffffcccc, 0xaa00aa00aa00aa00,
    0xf0f0f0f000000000, 0xcccc0000cccc0000, 0xffaaffaaf0a0f0a0, 0xffaacc88f0a0c080,
    0xfaf0faf0aa00aa00, 0xfefcfaf0eeccaa00, 0xa000a00000000000, 0xc8c0000088000000,
    0xe8c0a00088000000, 0xfea8c880e0808000, 0xfee8e880e8808000, 0xfeeaeaaaeaaaaaaa,
    0xfeeeeeeeeeeeeeee, 0xfef8f8f0f8f0f0f0, 0xfff8fff0fff0fff0, 0xffffe880ffff8000,
    0xffffffffffff8000, 0xfee8eee0eee0eee0, 0xfee8eee0eee08000, 0xaaa8a880a8808000,
    0xccc8c880c8808000, 0xeee8e880e8808000, 0xe0e0e080e0808000, 0xee00e800e8008000,
    0xeee0e880e8808000, 0xeee00000e8800000, 0xeee0e88000000000, 0xeee0e880e8800000,
    0xeee0eee0eee00000
  ] : List ℕ).getD j.val 0

def twEncode (x : Fin 6 → Bool) : Fin 64 :=
  Fin.ofNat 64 ((if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) + (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0))

def twDecode (k : Fin 64) (p : Fin 6) : Bool := k.val.testBit p.val

def twF (j : Fin 33) (x : Fin 6 → Bool) : Bool := (twMask j).testBit (twEncode x).val

def twA (j p : Fin 6) : Bool := decide (p.val % 2 = j.val % 2)

def twB (j p : Fin 6) : Bool := decide (p.val / 2 ≠ j.val / 2)

open PEqualNP.CircuitLowerBounds

-- The first fifteen gates compute the threshold of four on six bits.
-- The next seventeen supply the two positive branches of the final output.
-- The last three gates select the branch using the negated threshold.
def compactGates : List Gate :=
  [
    ⟨.or, [0, 3]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [4, 1]⟩,
    ⟨.and, [0, 3]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [4, 1]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.and, [12, 8]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [14, 11]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.and, [14, 11]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [20, 0]⟩,
    ⟨.or, [21, 1]⟩,
    ⟨.or, [20, 2]⟩,
    ⟨.or, [23, 3]⟩,
    ⟨.or, [20, 4]⟩,
    ⟨.or, [25, 5]⟩,
    ⟨.and, [22, 24]⟩,
    ⟨.and, [27, 26]⟩,
    ⟨.and, [20, 0]⟩,
    ⟨.and, [20, 1]⟩,
    ⟨.or, [29, 30]⟩,
    ⟨.and, [31, 2]⟩,
    ⟨.and, [31, 3]⟩,
    ⟨.or, [32, 33]⟩,
    ⟨.and, [34, 4]⟩,
    ⟨.and, [34, 5]⟩,
    ⟨.or, [35, 36]⟩,
    ⟨.not, [20]⟩,
    ⟨.and, [28, 38]⟩,
    ⟨.or, [39, 37]⟩
  ]

def compactOut (i : Fin 33) : ℕ := if i.val < 32 then 6 + i.val else 40

theorem compactSize : compactGates.length = 35 := by decide

theorem compactLegal : ∀ g ∈ compactGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  let ok := fun g : Gate =>
    (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)
  have checked : compactGates.all ok = true := by decide
  intro g hg
  have h := List.all_eq_true.mp checked g hg
  cases e : g.op <;> simp_all [ok]

lemma compactIdx (t : Fin compactGates.length) (h : (compactGates.get t).op = GateOp.not) :
    t = ⟨32, by decide⟩ := by
  fin_cases t <;> first | rfl | contradiction

theorem compactOne : ∀ i j : Fin compactGates.length,
    (compactGates.get i).op = GateOp.not → (compactGates.get j).op = GateOp.not → i = j := by
  exact fun i j hi hj => (compactIdx i hi).trans (compactIdx j hj).symm

theorem compactCorrect : ∀ (i : Fin 33) (x : Fin 6 → Bool),
    Circuit.eval ⟨compactGates, compactOut i⟩ (List.ofFn x) = twF i x := by
  decide +kernel

theorem compactThreshold : ∀ t : Fin compactGates.length, (compactGates.get t).op = GateOp.not →
    ∃ a k : ℕ, (compactGates.get t).inputs.head? = some a ∧ ∀ x : Fin 6 → Bool,
      (Circuit.wires ⟨compactGates, 0⟩ (List.ofFn x)).getD a false =
        decide (k ≤ (Finset.univ.filter (fun i : Fin 6 => x i = true)).card) := by
  have idx : ∀ t : Fin compactGates.length, (compactGates.get t).op = GateOp.not →
      (compactGates.get t).inputs.head? = some 20 := by
    intro t ht
    rw [compactIdx t ht]
    rfl
  have correct : ∀ x : Fin 6 → Bool, (Circuit.wires ⟨compactGates, 0⟩ (List.ofFn x)).getD 20 false =
      decide (4 ≤ (Finset.univ.filter (fun i : Fin 6 => x i = true)).card) := by decide +kernel
  exact fun t ht => ⟨20, 4, idx t ht, correct⟩

-- Each pair of test inputs makes exactly one raw input fall from true to false.
theorem twPositiveChecked : ∀ i : Fin 32, twF i.castSucc (fun _ => true) = true := by
  decide +kernel

theorem twReserveChecked : ∀ (i : Fin 32) (j : Fin 6),
    twF i.castSucc (twA j) = true → twF i.castSucc (twB j) = true := by
  decide +kernel

theorem twFallChecked : ∀ j : Fin 6,
    twF (Fin.last 32) (twA j) = true ∧ twF (Fin.last 32) (twB j) = false := by
  decide +kernel

theorem twSourceChecked : ∀ (j p : Fin 6),
    twA j p = true → twB j p = false → p = j := by
  decide +kernel

def twDifference (s t : ℕ) : Fin 64 := Fin.ofNat 64 (Nat.log2 (s ^^^ t))

def twVarTable (p : Fin 6) : ℕ :=
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00,
    0xffff0000ffff0000, 0xffffffff00000000] : List ℕ).getD p.val 0

theorem twNonprojChecked : ∀ (i : Fin 32) (p : Fin 6),
    ∃ x, twF i.castSucc x ≠ x p := by
  have h : ∀ (i : Fin 32) (p : Fin 6),
      let x := twDecode (twDifference (twMask i.castSucc) (twVarTable p))
      twF i.castSucc x ≠ x p := by decide +kernel
  exact fun i p => ⟨_, h i p⟩

theorem twDistinctChecked : ∀ i j : Fin 32, i ≠ j →
    ∃ x, twF i.castSucc x ≠ twF j.castSucc x := by
  have h : ∀ i j : Fin 32, i ≠ j →
      let x := twDecode (twDifference (twMask i.castSucc) (twMask j.castSucc))
      twF i.castSucc x ≠ twF j.castSucc x := by decide +kernel
  exact fun i j hij => ⟨_, h i j hij⟩

-- A disjunction of positive conjunctions certifies each output is monotone.
def twTerms (j : Fin 33) : List ℕ :=
  ([
    [1, 8],
    [4, 32],
    [2, 16],
    [9],
    [36],
    [18],
    [5, 12, 33, 40],
    [7, 14, 21, 28, 35, 42, 49, 56],
    [9, 36],
    [9, 18, 36],
    [45],
    [27, 54],
    [27, 45, 54],
    [15, 23, 29, 30, 39, 43, 46, 51, 53, 57, 58, 60],
    [15, 23, 27, 29, 30, 39, 43, 45, 46, 51, 53, 54, 57, 58, 60],
    [1, 30, 46, 54, 58, 60],
    [1, 2, 60],
    [4, 27, 43, 51, 57, 58],
    [4, 8, 51],
    [15, 16, 39, 43, 45, 46],
    [15, 16, 32],
    [5, 6, 9, 10, 51, 60],
    [15, 21, 22, 25, 26, 37, 38, 41, 42, 51, 60],
    [15, 23, 27, 29, 39, 43, 45, 51, 53, 57],
    [15, 23, 27, 30, 39, 43, 46, 51, 54, 58],
    [15, 23, 27, 29, 30, 39, 43, 45, 46, 51, 53, 54, 57, 58],
    [15, 23, 29, 30, 39, 45, 46, 53, 54],
    [15, 27, 29, 30, 43, 45, 46, 57, 58],
    [15, 23, 27, 29, 30, 39, 43, 45, 46, 53, 54, 57, 58],
    [23, 27, 29, 30, 53, 54, 57, 58],
    [39, 43, 45, 46, 53, 54, 57, 58],
    [23, 27, 29, 30, 39, 43, 45, 46, 53, 54, 57, 58],
    [21, 22, 25, 26, 37, 38, 41, 42]
  ] : List (List ℕ)).getD j.val []

def twTerm (t : ℕ) (x : Fin 6 → Bool) : Bool :=
  decide (∀ p : Fin 6, t.testBit p.val = true → x p = true)

theorem twDecodeEncode : ∀ (x : Fin 6 → Bool) (i : Fin 6), twDecode (twEncode x) i = x i := by
  decide +kernel

theorem twMonoChecked (j : Fin 33) (x y : Fin 6 → Bool) (h : ∀ p, x p ≤ y p) :
    twF j x ≤ twF j y := by
  have cert : ∀ (i : Fin 33) (k : Fin 64),
      twF i (twDecode k) = (twTerms i).any (fun t => twTerm t (twDecode k)) := by decide +kernel
  have representation (v : Fin 6 → Bool) :
      twF j v = (twTerms j).any (fun t => twTerm t v) := by
    have e : twDecode (twEncode v) = v := funext (twDecodeEncode v)
    simpa only [e] using cert j (twEncode v)
  rw [representation x, representation y]
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨t, ht, hv⟩ := List.any_eq_true.mp hx
  refine List.any_eq_true.mpr ⟨t, ht, ?_⟩
  apply decide_eq_true
  have htx : ∀ p : Fin 6, t.testBit p.val = true → x p = true := of_decide_eq_true hv
  exact fun p hp => Bool.le_iff_imp.mp (h p) (htx p hp)

end PEqualNP.Outside.L_meta_1037

open PEqualNP.Outside.L_meta_1037 in
theorem PEqualNP.Outside.L_meta_1037 : ∃ (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool), n ≤ 6 ∧ (∀ (j : Fin m) (x y : Fin n → Bool), (∀ i : Fin n, x i ≤ y i) → f j x ≤ f j y) ∧ ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out j⟩ (List.ofFn x) = f j x) ∧ (∀ t : Fin gates.length, (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ a k : ℕ, (gates.get t).inputs.head? = some a ∧ ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD a false = decide (k ≤ (Finset.univ.filter (fun i : Fin n => x i = true)).card)) ∧ ∀ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' j⟩ (List.ofFn x) = f j x) → gates.length < gates'.length := by
  refine ⟨6, 33, twF, by decide, twMonoChecked, compactGates, compactOut,
    compactLegal, compactOne, compactCorrect, compactThreshold, ?_⟩
  intro gates out hlegal heval
  have bound := reserveBound (r := 32) twF twA twB (fun i => ⟨_, twPositiveChecked i⟩)
    twNonprojChecked twDistinctChecked twReserveChecked twFallChecked twSourceChecked
    gates out hlegal heval
  rw [compactSize]
  omega
