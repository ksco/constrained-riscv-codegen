import z3

x = z3.Int("x")
y = z3.Int("y")
z3.solve(x > 2, y < 10, x + 2 * y == 7)
