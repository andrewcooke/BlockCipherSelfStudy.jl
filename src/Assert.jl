
module Assert
export assert3

# if the expression has 3 parts then it is assumed to be similar to
# 'left == right' and the leftand right halves will be evaluated and
# displayed on failure.  otherwise, behaviour as for @assert
macro assert3(expr)
    # the $(report(...)) delays evaluation until failure
    :($expr ? nothing : error("Assertion failed: ", $(report(expr))))
end

function report(expr)
    if length(expr.args) != 3
        return string(expr)
    else
        left = eval(expr.args[1])
        right = eval(expr.args[3])
        return "$(left) [!$(expr.args[2])] $(right)"
    end
end

function tests()
    @assert3 1 == 1    # succeeeds
    @assert3 1 == 1+1  # prints 1 [!==] 2
end

tests()

end
