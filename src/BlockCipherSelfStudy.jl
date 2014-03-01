
module BlockCipherSelfStudy
using Assert, Blocks, DES, RC5

function tests()
    Assert.tests()
    Blocks.tests()
    DES.tests()
    RC5.tests()
end

end
