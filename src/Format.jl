
module Format
export bin8


function bin8{U<:Unsigned}(val::U; n=0)
    n = n == 0 ? 8 * sizeof(U) : n
    s = bin(val)
    while length(s) < n
        s = "0$s"
    end
    if length(s) > n
        s = s[end-n+1:end]
    end
    w = ""
    while length(s) > 0
        l = min(length(s), 8)
        w = "$(s[end-l+1:end]) $w"
        s = s[1:end-l]
    end
    w
end

end
