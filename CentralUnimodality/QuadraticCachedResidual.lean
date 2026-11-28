module

public import CentralUnimodality.QuadraticResidualProducts

/-! Identify both saved physical rows with the original signed residual evaluator. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial.QuadraticInputs
open RationalPolyRow

theorem even_row : quadraticResidualRow 0=evenResidual := by
  have select : (if (0:ℕ)=0 then evenRawM else oddRawM)=evenRawM := rfl
  rw [← evenResidual_exact]
  unfold quadraticResidualRow
  rw [select]
  simp only [fromTrials,RationalPolyRow.residual,splitFirst,splitSecond,assemble,
    bridge_exact,trial_exact,free_exact,evenM_exact,bOne_exact,bTwo_exact,pEven_exact,
    gEven_exact,leadingBF_exact,leadingEven_exact,secondBF_exact,secondEven_exact,third12_exact,
    third21_exact,fourth22_exact,firstBF_exact,firstEven_exact,secondBFBase_exact]

theorem odd_row : quadraticResidualRow 1=oddResidual := by
  have select : (if (1:ℕ)=0 then evenRawM else oddRawM)=oddRawM := rfl
  rw [← oddResidual_exact]
  simp only [quadraticResidualRow,fromTrials,RationalPolyRow.residual,splitFirst,splitSecond,assemble,
    select,bridge_exact,trial_exact,free_exact,oddM_exact,bOne_exact,bTwo_exact,
    pOdd_exact,gOdd_exact,leadingBF_exact,leadingOdd_exact,secondBF_exact,secondOdd_exact,third12_exact,
    third21_exact,fourth22_exact,firstBF_exact,firstOdd_exact,secondBFBase_exact]

end CentralUnimodality.PolynomialTrial.QuadraticInputs
