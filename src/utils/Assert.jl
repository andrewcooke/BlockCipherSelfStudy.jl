
module Assert

export @assert3, @assert3f


# if the expression has 3 parts then it is assumed to be similar to
# 'left == right' and the left and right halves will be evaluated and
# displayed on failure.
macro assert3(expr)
    doassert(string, expr)
end

# as above, but with a function that is used to format results 
# (for example, hex would hexify numerical values).
macro assert3f(fmt, expr)
    doassert(fmt, expr)
end

function doassert(fmt, expr)
    if length(expr.args) != 3
        error("Expected $expr to contain 3 components")
    end
    :($(esc(expr)) ? nothing : error("Assertion failed: ",
                                     $fmt($(esc(expr.args[1]))), 
                                    " [!",
                                     string($(esc(expr.args[2]))), 
                                     "] ",
                                     $fmt($(esc(expr.args[3])))))
end



function tests()
    function noisy1()
        println("called!")
        return 1
    end
    @assert3 1 == 1           # succeeeds
    println("runtime")
#    @assert3 1 == 1+noisy1()  # prints 1 [!==] 2
#    println("Assert.tests ok")
end

#tests()

end
