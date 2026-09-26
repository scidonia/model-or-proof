import LCR-r1
#check LCR.succ
#check LCR.Process
#check LCR.State
open LCR
#check succ
#check Process
example (hN : 2 ≤ N) (i : Process N) : LCR.succ i ≠ i := by
  intro h
  have hval : (i.val + 1) % N = i.val := by
    simpa [LCR.succ] using congrArg Fin.val h
  omega
