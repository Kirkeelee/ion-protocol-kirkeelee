use builtin rule sanity;

function cvlMulDiv(uint x, uint y, uint denominator) returns uint {
    require(denominator != 0);
    return require_uint256(x*y/denominator);
}

definition RAY() returns uint256 = 10^27;


rule calculateInterestRate {
    env e;
    uint256 ilkIndex;
    uint256 totalIlkDebt;
    uint256 totalEthSupply;
    uint256 minimumborrowrate;
    uint256 scalefactor;

    minimumborrowrate, scalefactor = calculateInterestRate(e,ilkIndex, totalIlkDebt, totalEthSupply);

    assert minimumborrowrate < RAY();

}