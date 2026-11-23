import Rasso.Laws.SolJoin

/-!
# Rasso: well-formed members of a solution set

`Sol.MembersOk s` says that every member of `s` is the graph of a function from the Data's
tuples to tuples with exactly the Decision's attributes. The membership theorem for ⋈_sol
(`Rasso.Laws.SolJoinComplete`) needs it.
-/

namespace Rasso

/-- `t` is sorted by attribute and its attributes are exactly `as`. -/
def Tuple.Exactly (as : List String) (t : Tuple) : Prop :=
  Tuple.Over as t ∧ ∀ a ∈ as, a ∈ t.map (·.1)

/-- Every member of the solution set is the graph of a function on its Data whose values
have exactly the Decision's attributes. -/
structure Sol.MembersOk (s : Sol) : Prop where
  dataAttrs : ∀ a ∈ s.data.attrs, a ∈ s.heading.attrs
  dataExact : ∀ d ∈ s.data.tuples, Tuple.Exactly s.data.attrs d
  graph : ∀ c ∈ s.candidates, ∃ f : Tuple → Tuple,
    (∀ d ∈ s.data.tuples, Tuple.Exactly s.decision.attrs (f d)) ∧
    c.body = (Rasso.graph s.heading s.data.tuples f).body

namespace SolJoinLaws

/-! ## σ_sol keeps it -/

/-- A solution set with the same Data and heading and fewer members keeps `MembersOk`. -/
theorem membersOk_of_sublist {s s' : Sol} (hs : s.MembersOk) (hd : s'.data = s.data)
    (hh : s'.heading = s.heading) (hc : s'.candidates.Sublist s.candidates) : s'.MembersOk := by
  have hdec : s'.decision = s.decision := by unfold Sol.decision; rw [hd, hh]
  refine ⟨?_, ?_, ?_⟩
  · rw [hd, hh]; exact hs.dataAttrs
  · rw [hd]; exact hs.dataExact
  · intro c hc'
    rw [hd, hh, hdec]
    exact hs.graph c (hc.subset hc')

theorem sigmaSol_membersOk {env : Env} {tg : List Expr} {c : Cond} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.sigmaSol c e).beq = false)
    (h : Expr.eval env tg (.sigmaSol c e) = .ok v) {s : Sol}
    (he : Expr.eval env tg e = .ok (.sol s)) (hs : s.MembersOk) :
    ∃ s', v = .sol s' ∧ s'.MembersOk := by
  obtain ⟨s0, s', he0, rfl, hd, hh, hsub⟩ := SolLaws.sigmaSol_keeps hnt h
  rw [he] at he0
  injection he0 with he0
  injection he0 with he0
  subst he0
  exact ⟨s', rfl, membersOk_of_sublist hs hd hh hsub⟩

/-! ## ω_sol gives it, for a well-formed Data and a decision heading with no attribute twice -/

theorem attrs_append (h k : Heading) : (h ++ k).attrs = h.attrs ++ k.attrs := by
  simp [Heading.attrs]

/-- The Decision of ω_sol's solution set is the decision's heading. -/
theorem decision_omegaSol {data : Finrel} {u : Unrel} (hdx : ∀ a ∈ u.heading.attrs, a ∉ data.attrs) :
    (Sol.decision ⟨data, data.heading ++ u.heading, []⟩) = u.heading := by
  unfold Sol.decision
  simp only
  rw [List.filter_append]
  have h1 : data.heading.filter (fun p => !data.attrs.contains p.1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have : p.1 ∈ data.attrs := List.mem_map_of_mem hp
    simpa using this
  have h2 : u.heading.filter (fun p => !data.attrs.contains p.1) = u.heading := by
    apply List.filter_eq_self.mpr
    intro p hp
    have : p.1 ∉ data.attrs := hdx p.1 (List.mem_map_of_mem hp)
    simpa using this
  rw [h1, h2, List.nil_append]

theorem omegaSol_membersOk {data : Finrel} {u : Unrel} {picks : List Tuple}
    (hwf : data.WF) (hn : u.heading.attrs.Nodup)
    (hdx : ∀ a ∈ u.heading.attrs, a ∉ data.attrs) (hp : u.tuples = .ok picks) :
    Sol.MembersOk ⟨data, data.heading ++ u.heading,
      omegaSolCandidates (data.heading ++ u.heading) data.tuples picks⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp only [attrs_append]
    exact List.mem_append_left _ ha
  · intro d hd
    have hf := hwf.fits d hd
    refine ⟨⟨hf.sorted, fun q hq => (hf.attrs q.1).mp (List.mem_map_of_mem hq)⟩, fun a ha => ?_⟩
    exact (hf.attrs a).mpr ha
  · intro c hc
    obtain ⟨f, hf, rfl⟩ := (mem_omegaSolCandidates (Finrel.nodup_tuples data) c).mp hc
    refine ⟨f, ?_, rfl⟩
    have hdec : (Sol.decision ⟨data, data.heading ++ u.heading,
        omegaSolCandidates (data.heading ++ u.heading) data.tuples picks⟩).attrs = u.heading.attrs := by
      have := decision_omegaSol (data := data) (u := u) hdx
      unfold Sol.decision at this ⊢
      simp only at this ⊢
      rw [this]
    rw [hdec]
    intro d hd
    obtain ⟨⟨ps, hps, e⟩, _⟩ := (Unrel.mem_tuples hp (f d)).mp (hf d hd)
    rw [e]
    refine ⟨hps.over hn, fun a ha => ?_⟩
    have hk : a ∈ ps.reverse.map (·.1) := by rw [List.map_reverse, hps.keys]; exact List.mem_reverse.mpr ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hk
    exact List.mem_map_of_mem ((List.mergeSort_perm _ _).mem_iff.mpr hq)

end SolJoinLaws
end Rasso
