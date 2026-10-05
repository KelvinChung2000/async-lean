import AsyncLean.Auto.Simplex
open AsyncLean
-- minimise x + y s.t. x + 2y = 4, x - y = 1  -> x=2, y=1
#eval Simplex.solve #[#[1, 2], #[1, -1]] #[4, 1] #[1, 1]
-- infeasible: x + y = -1
#eval Simplex.solve #[#[1, 1]] #[-1] #[1, 1]
-- min x s.t. x - y = 0, y = 3 -> x = 3
#eval Simplex.solve #[#[1, -1], #[0, 1]] #[0, 3] #[1, 0]
