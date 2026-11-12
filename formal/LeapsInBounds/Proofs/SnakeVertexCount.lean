module

public import LeapsInBounds.Statements.SnakeInTheBox
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-!
# Trivial upper bounds for snakes and coils

The vertices of a snake or a coil are distinct vertices of `Q_n`, of which
there are `2^n`. So a snake has length at most `2^n - 1`, and a coil at most
`2^n`.
-/

public section

namespace LeapsInBounds.Proofs.SnakeVertexCount

open LeapsInBounds.SnakeInTheBox

theorem snake (n : ℕ) : UpperBound n (2 ^ n - 1) := by
  intro m p hp
  have := Fintype.card_le_of_injective p hp.1
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at this
  omega

theorem coil (n : ℕ) : CoilUpperBound n (2 ^ n) := by
  intro m c hc
  have := Fintype.card_le_of_injective c hc.2.1
  simpa using this

theorem upper_1 : UpperBound 1 1 := snake 1
theorem upper_2 : UpperBound 2 3 := snake 2
theorem upper_3 : UpperBound 3 7 := snake 3
theorem upper_4 : UpperBound 4 15 := snake 4
theorem upper_5 : UpperBound 5 31 := snake 5
theorem upper_6 : UpperBound 6 63 := snake 6
theorem upper_7 : UpperBound 7 127 := snake 7
theorem upper_8 : UpperBound 8 255 := snake 8
theorem upper_9 : UpperBound 9 511 := snake 9
theorem upper_10 : UpperBound 10 1023 := snake 10
theorem upper_11 : UpperBound 11 2047 := snake 11
theorem upper_12 : UpperBound 12 4095 := snake 12
theorem upper_13 : UpperBound 13 8191 := snake 13

theorem coil_upper_2 : CoilUpperBound 2 4 := coil 2
theorem coil_upper_3 : CoilUpperBound 3 8 := coil 3
theorem coil_upper_4 : CoilUpperBound 4 16 := coil 4
theorem coil_upper_5 : CoilUpperBound 5 32 := coil 5
theorem coil_upper_6 : CoilUpperBound 6 64 := coil 6
theorem coil_upper_7 : CoilUpperBound 7 128 := coil 7
theorem coil_upper_8 : CoilUpperBound 8 256 := coil 8
theorem coil_upper_9 : CoilUpperBound 9 512 := coil 9
theorem coil_upper_10 : CoilUpperBound 10 1024 := coil 10
theorem coil_upper_11 : CoilUpperBound 11 2048 := coil 11
theorem coil_upper_12 : CoilUpperBound 12 4096 := coil 12
theorem coil_upper_13 : CoilUpperBound 13 8192 := coil 13

end LeapsInBounds.Proofs.SnakeVertexCount
