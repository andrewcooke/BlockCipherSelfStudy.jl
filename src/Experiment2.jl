
module Experiment2
export foo, bar

function bar(x)
    foo(x)
end

function foo(x)
    println("base")
end

end

module Baz
using Experiment2

function Experiment2.foo(x::Float64)
    println("float")
end

function test()
    function Experiment2.foo(x::Int)
        println("int")
    end
    bar(1.0)  # works (prints "float")
    bar(1)  # THIS PRINTS "base" WHEN I WANT "int"
end

test()

end
