export Nat, Zero, Succ
export zero_ne_succ, succ_inj
export Zero, One, Two, Three, Four
export Add, add_zero, add_succ

# All the natural numbers stuff
struct Nat <: Ty end

Natural = Term{Nat}

# Define the basic natural numbers via Zero and Succ (from Peano's axioms).
# Zero is the base case, and Succ is a constructor that takes a natural number
# and produces the next natural number.
struct Zero <: Natural end
struct Succ{N <: Natural} <: Natural
    n::N
end
# (An interesting observation here is that very large natural numbers are
# represented as deeply nested Succ structures. This is not very efficient since
# Julia isn't really built for this, but it'll do; of course, there are other
# equivalent representations which would suffice.)

# Pretty printing for natural numbers
function Base.show(io::IO, ::Zero)
    print(io, "0")
end

function Base.show(io::IO, n::Succ{<: Natural})
    print(io, "S(")
    show(io, n.n)
    print(io, ")")
end

# Axioms for succ
zero_ne_succ(::Eq{Zero, <: Succ{<: Natural}}) = False()
# The injectivity of succ: if S(n) = S(m), then n = m
succ_inj(p::Eq{<: Succ{<: Natural}, <: Succ{<: Natural}}) = Eq(p.lhs.n, p.rhs.n)

# Define some specific natural number types for convenience
const One = Succ{Zero}
const Two = Succ{One}
const Three = Succ{Two}
const Four = Succ{Three}

# Addition
struct Add{T <: Natural, U <: Natural} <: Natural
    x::T
    y::U
end

# Pretty printing for addition
function Base.show(io::IO, add::Add{<: Natural, <: Natural})
    show(io, add.x)
    print(io, " + ")
    show(io, add.y)
end

add_zero(x::Natural) = Eq(Add(x, Zero()), x)
add_succ(x::Natural, y::Natural) = Eq(Add(x, Succ(y)), Succ(Add(x, y)))