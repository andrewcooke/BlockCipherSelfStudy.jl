
module Tasks

export take, repeat, constant, counter, chain


function take(n, source)
    Task() do
        while n > 0
            produce(consume(source))
            n = n - 1
        end
    end
end

function repeat(f)
    Task() do
        while true
            produce(f())
        end
    end
end

function constant(n)
    repeat(() -> n)
end

function counter(start=0)
    repeat() do
        save = start
        start = start + 0x1
        save
    end
end

function chain(tasks...)
    Task() do
        for task in tasks
            for value in task
                produce(value)
            end
        end
    end
end

end

