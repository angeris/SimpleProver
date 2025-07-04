using Base: show

export refl, symm, trans, map_eq

struct False end

# The basic "universal" type from which everything is derived.  Enough for
# Peano, but not for universal quantification or really anything more complex.
abstract type Ty end

# A _term_ is an expression of a given type; for example, a "general" natural
# number will be a term of type `Nat` (defined in `naturals.jl`)
abstract type Term{T <: Ty} end

# This struct captures a _statement_ which claims equality between lhs and rhs.
struct Eq{L <: Term{<: Ty}, R <: Term{<: Ty}} <: Term{Ty}
    lhs::L
    rhs::R
end

# Pretty printing for equality
function Base.show(io::IO, eq::Eq)
    show(io, eq.lhs)
    print(io, " = ")
    show(io, eq.rhs)
end


# Obviously, equality is reflexive, symmetric, and transitive
refl(t::Term) = Eq(t, t)
symm(eq::Eq) = Eq(eq.rhs, eq.lhs)
trans(eq1::Eq{U, V}, eq2::Eq{V, W}) where {U, V, W} = Eq(eq1.lhs, eq2.rhs)

# And equality means that two terms are equal after applying a function
map_eq(f::Function, eq::Eq) = Eq(f(eq.lhs), f(eq.rhs))