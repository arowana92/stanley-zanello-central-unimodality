module

public import CentralUnimodality.IntervalPolynomialSigns
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! Exact moments of the trial on the compact frequency interval.
After substituting frequency 512 t³, the monomial argument is t²/4. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial intervalIntegral

def quarterWeights : List ℤ → List ℤ × ℕ
  | [] => ([],1)
  | c::a =>
    let (p,s) := quarterWeights a
    ((c*(4*s:ℕ))::p,4*s)

theorem quarter_scale (a : List ℤ) : (quarterWeights a).2=4^a.length := by
  induction a with
  | nil => rfl
  | cons c a ih => simp [quarterWeights,ih,pow_succ,mul_comm]

def unitNumerator (q : ℕ → ℕ) : List ℤ → ℕ → ℤ
  | [], _ => 0
  | c::a, k => c*(q (k+1):ℤ)+unitNumerator q a (k+2)

noncomputable def unitMoment (a : List ℤ) (k : ℕ) : ℝ :=
  ∫ t in (0:ℝ)..1, t^k*(realDense a).eval (t^2/4)

private theorem moment_step (c : ℤ) (a : List ℤ) (k : ℕ) :
    unitMoment (c::a) k=(c:ℝ)/(k+1)+unitMoment a (k+2)/4 := by
  have eq (t : ℝ) : t^k*(realDense (c::a)).eval (t^2/4)=
    t^k*(c:ℝ)+(t^(k+2)*(realDense a).eval (t^2/4))/4 := by
    simp only [realDense,densePoly,Polynomial.map_add,Polynomial.map_C,Polynomial.map_mul,map_X,
      eval_add,eval_mul,eval_C,eval_X,Int.coe_castRingHom,pow_add]
    ring
  have hcont : Continuous (fun t : ℝ => (realDense a).eval (t^2/4)) :=
    (realDense a).continuous.comp (by fun_prop)
  simp only [unitMoment,eq]
  rw [integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),integral_div,integral_mul_const,integral_pow]
  simp
  ring

theorem unitMoment_cleared (q : ℕ → ℕ) {D top : ℕ}
    (hq : ∀ j, 0<j → j≤top → q j*j=D) (a : List ℤ) (k : ℕ) (h : k+2*a.length≤top) :
    (D:ℝ)*(4:ℝ)^a.length*unitMoment a k=(unitNumerator q (quarterWeights a).1 k:ℝ) := by
  induction a generalizing k with
  | nil => simp [unitMoment,realDense,densePoly,quarterWeights,unitNumerator]
  | cons c a ih =>
    have bound := hq (k+1) (by omega) (by simp only [List.length_cons] at h; omega)
    have div : (D:ℝ)/((k:ℝ)+1)=q (k+1) := by
      apply (div_eq_iff (by positivity : (k:ℝ)+1≠0)).mpr
      exact_mod_cast bound.symm
    have tail := ih (k+2) (by simp only [List.length_cons] at h; omega)
    rw [moment_step]
    simp only [List.length_cons,pow_succ,quarterWeights,quarter_scale,unitNumerator,Int.cast_add,
      Int.cast_mul,Int.cast_natCast,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [← tail,← div]; push_cast; ring

def denomLcm : ℕ → ℕ
  | 0 => 1
  | n+1 => (denomLcm n).lcm (n+1)

theorem dvd_denomLcm {k n : ℕ} (hk : 0<k) (h : k≤n) : k∣denomLcm n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [denomLcm]
    rcases Nat.eq_or_lt_of_le h with eq|lt
    · exact eq ▸ Nat.dvd_lcm_right _ _
    · exact (ih (by omega)).trans (Nat.dvd_lcm_left _ _)

theorem denomLcm_pos (n : ℕ) : 0<denomLcm n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [denomLcm]
    exact Nat.lcm_pos ih (Nat.succ_pos _)

def common4000 : ℕ := 49595048273321086406439433293821300563114024320579444653249675982994439153218574866639617896290542887981121843003170168992727811474970641425595878707022420361402876502883108901108421832034836798122314425118892059437162944180438903031175242141287314729042927267856184240597877266612282822044654351001501850523023708640838926775529073064895259439992211302648061420404924702162236897941131803640158658045216076713783201152646162363542426218376562725881329364901216480188702165980094907963971070443681111074371849871637216914512811036727012902455301817102476092182445894994172109055038716576810656844012437830824509261975128238234659611430493126417976113923161017556747729224320395211290382902670615299997365801634752832567993790638794046508128817577011712942545553549604434956603679022249737003494212241794602447269453316971076674207609399866174234659946692394581723719619592084471904828964069154976361175783830019229513958191644578287599404823881849869731871824413284968269907919158888601572288185904441039732430033558855067878170622597798398259776171040715913920682587692911010114923429377026601580826495765835975663809561760382810986078642722673673452250689415047121988271404922222132754920676800904663621101506735802195566179480694179102184983139680727020607932382219251943354748986802110948519693652199120708491249470143250056624970789627581015525593015095992090189490252510199359893742473657917944208624667998995327296878401813900198415265501361191528839920310701618912571210966211896973936629339158726943427796051603038214109633403793976205600549327411069980218559045826799852368278636675576821911732488799549649003936898184487549307862677588861207413207357798134947333936013292381278583175571310736915056010723130249380217600000

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem common4000_check : ((List.range 4000).all (fun j => common4000%(j+1)==0))=true := by decide +kernel

def momentDivisor (top : ℕ) := if top≤4000 then common4000 else denomLcm top

theorem momentDivisor_pos (top : ℕ) : 0 < momentDivisor top := by
  unfold momentDivisor; split
  · decide +kernel
  · exact denomLcm_pos _

theorem reciprocal_exact {j top : ℕ} (hj : 0<j) (h : j≤top) :
    momentDivisor top/j*j=momentDivisor top := by
  apply Nat.div_mul_cancel
  unfold momentDivisor; split
  · apply Nat.dvd_of_mod_eq_zero
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    exact eq_of_beq (List.all_eq_true.mp common4000_check i (List.mem_range.mpr (by omega)))
  · exact dvd_denomLcm hj h

end CentralUnimodality.PolynomialTrial
