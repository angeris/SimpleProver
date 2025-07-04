using SimpleProver

# --- Goal: Prove that 1 = 1
GoalType = SimpleProver.Eq{One, One}
# This one is easy of course
one = Succ(Zero()) # 1 = S(0)
one_eq_one = refl(one) # 1 = 1
@assert one_eq_one isa GoalType

# --- Goal: Prove that 1+1 = 2
GoalType = SimpleProver.Eq{Two, Add{One, One}}
# This one is also easy-ish
zer = Zero()
one = Succ(zer)
two = Succ(one)

# For fun, note that the types make sense and are 'inhabited'
@assert zer isa Zero
@assert one isa One
@assert two isa Two

# Fine, onto the actual proof:
# `map_eq` applies a function to both sides of an equality, `add_zero(n)` is the equality that $n + 0 = n$ (axiom)
succ_one_plus_zero_eq_two = map_eq(x -> Succ(x), add_zero(one))
# `add_succ` is the assumption that $n + S(m) = S(n + m)$
one_plus_one_eq_succ_one_plus_zero = add_succ(one, zer)
# Finally, we can use `trans` to combine these two equalities and `symm` to reverse the order
final_case = symm(trans(one_plus_one_eq_succ_one_plus_zero, succ_one_plus_zero_eq_two)) 

# Which proves the final goal that 1 + 1 = 2
@assert final_case isa GoalType

# --- Goal: prove that S(n) = n + 1 for any n
GoalType = SimpleProver.Eq{Succ{N}, Add{N, One}} where N
# Note that this is a _generic_ goal, meaning that we have a free variable. This corresponds
# to a function taking any natural number `n` and returning the equality `S(n) = n + 1`.
# This proof will be similar to the previous, but applied for any natural number `n`.
function succ_add_one(n)::GoalType
    n_plus_succ_zero = add_succ(n, Zero()) # n + S(0) = S(n + 0)
    one_plus_succ = map_eq(x -> Succ(x), add_zero(n)) # S(n + 0) = S(n)

    symm(trans(n_plus_succ_zero, one_plus_succ)) # S(n) = n + 1
end

# The fact that this function compiles at all is a proof that it works since the
# types are checked at call time (which compiles the function). The specific
# case of `n = one` is exactly the one proven above.
@assert succ_add_one(one) isa GoalType
# But of course, we can check others
@assert succ_add_one(two) isa GoalType
four = Succ(Succ(two))
@assert succ_add_one(four) isa GoalType

# --- Goal: how about that 1 ≠ 2?
# By definition a ≠ b is a proof of `False` assuming `a=b`
GoalType = SimpleProver.False
# To do this, we have to cheat a little bit to be able to 'assume' that 1=2. An actual
# proof language would ensure that this is possible only when we wish to prove a contradiction,
# otherwise, users could (accidentally) assume something that is to be proven or that is false.
two_eq_one = SimpleProver.Eq(one, two)
one_eq_zero = succ_inj(two_eq_one) # S(0) = 0, which is a contradiction since S(n) is never equal to 0 for any n
@assert zero_ne_succ(one_eq_zero) isa GoalType
