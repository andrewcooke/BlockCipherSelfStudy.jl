
module GA
using Debug
export Population, evolve

# prepare!(population) -> nothing
# score(context, individual) -> score
# select(population) -> individual
# breed(context, individual, individual) -> individual
# mutate(context, individual) -> individual  (can modify argument)
# complete(age, population) -> bool

prepare!(p::Nothing) = nothing
breed(c::Nothing, i1, i2) = i1
mutate(c::Nothing, i) = i
complete(a, p::Nothing) = true
score(p::Nothing) = nothing
select(p::Nothing) = nothing

function score_and_pair(context)
    individual -> (score(context, individual), individual)
end

type Population{C,I,S}
    context::C
    generation::Int
    size::Int
    n_children::Int
    sorted::Array{(S,I),1}
end

function Population{C,I,S}(context::C, popn::Array{I,1}, n_children, ::Type{S})
    @assert length(popn) >= n_children
    sorted = collect((S, I), pmap(score_and_pair(context), popn))
    sort!(sorted, rev=true)
    Population{C,I,S}(context, 0, length(popn), n_children, sorted)
end

function evolve{C,I,S}(popn::Population{C,I,S})
    while true
        start = tic()
        prepare!(popn)
        children = [mutate(popn.context,
                           breed(popn.context, select(popn), select(popn)))
                    for _ in 1:popn.n_children]
        scored = collect((S, I), pmap(score_and_pair(popn.context), children))
        splice!(popn.sorted, (popn.size-popn.n_children+1):popn.size, scored)
        sort!(popn.sorted, rev=true)
        popn.generation, age = popn.generation + 1, toc() - start
        if complete(age, popn) 
            return age, popn
        end
    end
end

end
