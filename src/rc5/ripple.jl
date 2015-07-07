
# ---- ripple diagrams


type Trace{W<:Unsigned}
    header::String
    value::Union(W, Nothing)
end

Trace{W<:Unsigned}(header::String, ::Type{W}) = Trace{W}(header, nothing)

=={W<:Unsigned}(t1::Trace{W}, t2::Trace{W}) = 
isequal(t1.header, t2.header) && isequal(t1.value, t2.value)


function encrypt{W<:Unsigned, R<:Rotation}(s::State{W, R}, a::W, b::W,
    trace::Vector{Trace{W}}; both=false)

    blank = Trace(" ", W)
    space() = push!(trace, blank)

    function push_maybe(trace, t)
        if length(trace) > 1 && trace[end] == blank && trace[end-1] == t
            pop!(trace)
        else
            push!(trace, t)
        end
    end

    function apply(f, op::String, arg1::W, head1::Union(String, Nothing), 
                   arg2::W, head2::String, head3::String)
        
        # re-use previous if possible for more compact display
        push_maybe(trace, Trace(head1, arg1))
        push!(trace, Trace(op, W))
        push!(trace, Trace(head2, arg2))
        result::W = f(arg1, arg2)
        space()
        push!(trace, Trace(head3, result))
        space()
        result
    end

    add(arg1::W, head1::String, arg2::W, head2::String) =
    apply(+, "+", arg1, head1, arg2, head2, head1)

    xor(arg1::W, head1::String, arg2::W, head2::String, head3::String) =
    apply($, "x", arg1, head1, arg2, head2, head3)

    rot(::Type{NoRotation}, arg1::W, head1::String, arg2::W, head2::String, i::Unsigned) =
    arg1

    function rot(::Type{RoundRotation}, arg1::W, head1::String, arg2::W, head2::String, i::Unsigned)
        push_maybe(trace, Trace(head1, arg1))
        push!(trace, Trace("^$(i)", W))
        result::W = rotatel(arg1, i)
        push!(trace, Trace(head1, result))
        space()
        result
    end

    rot(::Type{FullRotation}, arg1::W, head1::String, arg2::W, head2::String, i::Unsigned) =
    apply(rotatel, "<", arg1, head1, arg2, head2, head1)

    push!(trace, Trace("b", b))
    space()

    a::W = add(a, "a", s.s[1], "s0")
    b::W = both ? add(b, "b", s.s[2], "s1") : b + s.s[2]

    for i in 0x1:s.r

        a = xor(b, "b", a, "a", "a")
        a = rot(s.rotate, a, "a", b, "b", i)
        a = add(a, "a", s.s[2i+1], "s$(2i)")

        if both
            b = xor(a, "a", b, "b", "b")
            b = rot(s.rotate, b, "b", a, "a", i)
            b = add(b, "b", s.s[2i+2], "s$(2i+1)")
        else
            b = a $ b
            b = rotatel(s.rotate, b, a, i)
            b = b + s.s[2i+2]
        end

    end

    push_maybe(trace, Trace("a", a))

    a, b
end

function format_string!(chars, text)
    for (i, c) in enumerate(text)
        chars[i] = c
    end
end

function format{W<:Unsigned}(trace::Vector{Trace{W}}; 
                             title=true, range=1:0)
    if length(range) < 1
        range = 1:8*sizeof(W)
    end
    header = title ? 1 + maximum(map(t -> length(t.header), trace)) : 0
    height = header + length(range)
    width = 1 + length(trace)
    chars = Array(Char, width, height)
    fill!(chars, ' ')
    fill!(slice(chars, width, 1:height), '\n')
    for i in 1:width-1
        if trace[i].value != nothing
            format_string!(slice(chars, i, header+1:height), 
                           bits(trace[i].value)[range])
        else
            fill!(slice(chars, i, header+1:8:height), trace[i].header[1])
        end
        if title
            format_string!(slice(chars, i, 1:header), trace[i].header)
        end
    end
    chars
end

function trace{W<:Unsigned}(state::State{W}, a::W, b::W;
                            title=true, range=1:0, both=false)
    t = Array(Trace{W}, 0)
    encrypt(state, a, b, t, both=both)
    chars = format(t, title=title, range=range)
    return string(reshape(chars, length(chars))...)
end

function diff(c1, c2)
    w, h = size(c1)
    @assert (w, h) == size(c2)
    d = Array(Char, w, h)
    fill!(d, ' ')
    fill!(slice(d, w, 1:h), '\n')
    for i in 1:w
        for j in 1:h
            if c1[i, j] != c2[i, j]
                d[i, j] = c2[i, j]
            end
        end
    end
    d
end

@compat function print_delta{W<:Unsigned}(state::State{W}, ab::Vector{Tuple{W,W}};
                                  range=1:0, both=false, chain=false)
    t = Array(Trace{W}, 0)
    a, b = ab[1]
    encrypt(state, a, b, t, both=both)
    chars = format(t, title=true, range=range)
    println()
    println(string(reshape(chars, length(chars))...))

    reference = format(t, title=false, range=range)
    for (a, b) in ab[2:end]
        u = Array(Trace{W}, 0)
        encrypt(state, a, b, u, both=both)
        update = format(u, title=false, range=range)
        d = diff(reference, update)
        println(string(reshape(d, length(d))...))
        if chain
            reference = update
        end
    end
end

function prove_carry{W<:Unsigned}(::Type{W}, r::Uint8, s, nmax)

    # the idea here was that the final addition leaked information via
    # the carry.  but it doesn't.

    n_strong, n_weak = 0, 0
    for i in 1:nmax
        state = State(W, r, collect(Uint8, take(s, rands(Uint8))), 
                      rotate=NoRotation)
        a, b = collect(W, take(2, rands(W)))
        ap, bp = encrypt(state, a, b)
        a1, _ = encrypt(state, a $ one(W), b)
        a2, _ = encrypt(state, a $ one(W), b $ (one(W) << 1))
#        println("$a $ap $a1 $a2")
        if 0 == state.s[2r+1] & 0x1
            # if bit 0 of the final state added to a is zero then we will
            # one of a1 or a2 will not have a carry into bit 1
            if 0 != (ap $ a1) & 0x2 && 0 != (ap $ a2) & 0x2
#                println("\ncounter-example - both have carries")
#                print_delta(state, [(a, b), (a $ one(W), b), 
#                                    (a $ one(W), b $ (one(W) << 1))])
            else
                n_strong += 1
            end
        else
            # if bit 0 is 1 then a1 will always have a carry
            if 0 == (ap $ a1) & 0x2
#                println("\ncounter-example - no carry")
#                print_delta(state, [(a, b), (a $ one(W), b)])
            else
                n_weak += 1
            end
        end
    end
    println("carry count: $n_strong / $n_weak")
end

function prove_nonlinear{W<:Unsigned}(::Type{W}, r::Uint8, k, nmax)
    n_add, n_xor = 0, 0
    for i in 1:nmax
        state = State(W, r, collect(Uint8, take(k, rands(Uint8))), 
                      rotate=NoRotation)
        a, b, c, d = collect(W, take(4, rands(W)))
        p, q = encrypt(state, convert(W, a+c), convert(W, b+d))
        rs1 = encrypt(state, a, b)
        rs2 = encrypt(state, c, d)
        r = convert(W, rs1[1] + rs2[1])
        s = convert(W, rs1[2] + rs2[2])
        if p == r || q == s
            n_add += 1
            if p == r
#                println("add $(bits(p))   $(bits(a)) $(bits(c))")
            end
            if q == s
#                println("add $(bits(q))   $(bits(b)) $(bits(d))")
            end
        end
        p, q = encrypt(state, a$c, b$d)
        rs1 = encrypt(state, a, b)
        rs2 = encrypt(state, c, d)
        r::W = rs1[1] $ rs2[1]
        s::W = rs1[2] $ rs2[2]
        if p == r || q == s
            n_xor += 1
            if p == r
#                println("xor $(bits(p))   $(bits(a)) $(bits(c))")
            end
            if q == s
#                println("xor $(bits(q))   $(bits(b)) $(bits(d))")
            end
        end        
    end
    println("linear count: $n_add / $n_xor")
end


function test_trace()
    @assert Trace{Uint8}("a", nothing) == Trace{Uint8}("a", nothing)
    @assert Trace{Uint8}("a", 0x1) == Trace{Uint8}("a", 0x1)
    @assert Trace{Uint8}("a", 0x2) != Trace{Uint8}("a", 0x1)
    @assert Trace{Uint8}("a", 0x1) != Trace{Uint8}("b", 0x1)
    println(trace(State(Uint16, 0x3, zeros(Uint8, 16), rotate=NoRotation), 
                  0x0000, 0x0000))
    print_delta(State(Uint8, 0x3, zeros(Uint8, 16), rotate=NoRotation), 
                [(0x00, 0x00), (0x01, 0x00), (0x01, 0x02)])
    print_delta(State(Uint8, 0x3, zeros(Uint8, 16), rotate=RoundRotation), 
                [(0x00, 0x00), 
                 (0x01, 0x00), (0x03, 0x00), (0x07, 0x00), (0x0f, 0x00), 
                 (0x1f, 0x00), (0x3f, 0x00), (0x7f, 0x00), (0xff, 0x00)], 
                both=true, chain=true)
    println("test_trace ok")
end
