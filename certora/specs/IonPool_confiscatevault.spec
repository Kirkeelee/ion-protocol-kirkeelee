import "erc20.spec";

use builtin rule sanity;

methods {
    // Interest rate model
    function _.calculateInterestRate(uint256, uint256, uint256) external => DISPATCHER(true);
    function _.COLLATERAL_COUNT() external => DISPATCHER(true);

    // Spot oracle
    function _.getSpot() external => getSpotCVL() expect uint256;

    // Whitelist
    function _.isWhitelistedBorrower(uint8 ilkIndex, address poolCaller, address addr, bytes32[] proof) external => getWhitelistCVL(poolCaller) expect bool;
    function _.isWhitelistedLender(address poolCaller, address addr, bytes32[] proof) external => getWhitelistCVL(poolCaller) expect bool;

    // Chainlink
    function _.latestRoundData() external => latestRoundDataCVL() expect (uint80, int256, uint256, uint256, uint80);

    function _.getStETHByWstETH(uint256 amount) external => getStETHByWstETHCVL(amount) expect (uint256);

    // mulDiv summary for better run time
    function _.mulDiv(uint x, uint y, uint denominator) internal => mulDivCVL(x,y,denominator) expect uint;

    //from vat.spec

    function totalNormalizedDebt(uint8) external returns uint256 envfree; //Art
    function normalizedDebt(uint8, address) external returns uint256 envfree; //art
    function can(address, address) external returns uint256 envfree optional;
    function weth() external returns uint256 envfree; //dai
    function debt() external returns uint256;
    function dust(uint8) external returns uint256 envfree;
    function gem(uint8, address) external returns uint256 envfree;
    function collateral(uint8, address) external returns uint256 envfree; //ink
    function wethSupplyCap() external returns uint256 envfree optional; //Line
    function debtCeiling(uint8) external returns uint256 envfree; //line
    function rate(uint8) external returns uint256;
    function unbackedDebt(address) external returns uint256 envfree; //sin
    function vault(uint8, address) external returns uint256, uint256 envfree; //urns
    function totalUnbackedDebt() external returns uint256 envfree; //vice



    function isOperator(address,address) external returns bool envfree;
    function lastRateUpdate(uint8) external returns uint256 envfree;
    function getIlkAddress(uint256) external  returns address envfree;
    function ilkCount() external returns uint256 envfree;
    function getIlkIndex(address) external  returns uint8 envfree;
    function isAllowed(address, address) external returns bool envfree;
    function rateUnaccrued(uint8) external  returns uint256;
    function debtUnaccrued() external returns uint256;
    function addressContains(address ) external returns bool envfree;

    //dink=changeInCollateral; dart=changeInNormalizedDebt;
}

ghost uint80 roundId;
ghost int256 answer;
ghost uint256 startedAt;
ghost uint256 updatedAt;
ghost uint80 answeredInRound;

function latestRoundDataCVL() returns (uint80, int256, uint256, uint256, uint80) {
    return (roundId, answer, startedAt, updatedAt, answeredInRound);
}

ghost uint256 spot;

function getSpotCVL() returns uint256 {
    return spot;
}


ghost mapping(uint256 => uint256) getStETHByWstETH_Ghost;

ghost mapping(address => bool) isWhitelisted_Ghost;

function getWhitelistCVL(address user) returns bool {
    return isWhitelisted_Ghost[user];
}

function getStETHByWstETHCVL(uint256 amount) returns uint256 {
    return getStETHByWstETH_Ghost[amount];
}

function mulDivCVL(uint x, uint y, uint denominator) returns uint {
    require(denominator != 0);
    return require_uint256(x*y/denominator);
}

definition WAD() returns uint256 = 10^18;
definition RAY() returns uint256 = 10^27;

definition min_int256() returns mathint = -1 * 2^255;
definition max_int256() returns mathint = 2^255 - 1;
definition max_ilk() returns uint256 = 2^8;


rule confiscateVault(uint8 i, address u, address v, address w, int256 changeInCollateral, int256 changeInNormalizedDebt) {
    env e;

    uint8 otherIlk;
    require(otherIlk != i);
    uint8 otherIlkU; address otherUsrU;
    require(otherIlkU != i || otherUsrU != u);
    uint8 otherIlkV; address otherUsrV;
    require(otherIlkV != i || otherUsrV != v);
    address otherUsrW;
    require(otherUsrW != w);

    uint256 totalNormalizedDebtBefore = totalNormalizedDebt(i);
    uint256 totalNormalizedDebtOtherBefore = totalNormalizedDebt(otherIlk);
    uint256 collateralBefore = collateral(i, u); 
    uint256 rateBefore = rateUnaccrued(e, i);
    uint256 normalizedDebtBefore = normalizedDebt(i, u);
    uint256 normalizedDebtOtherBefore = normalizedDebt(otherIlkU, otherUsrU);
    uint256 gemBefore = gem(i, v);
    uint256 gemOtherBefore = gem(otherIlkV, otherUsrV);
    uint256 unbackedDebtBefore = unbackedDebt(w);
    uint256 unbackedDebtOtherBefore = unbackedDebt(otherUsrW);
    uint256 totalUnbackedDebtBefore = totalUnbackedDebt();

    confiscateVault(e, i, u, v, w, changeInCollateral, changeInNormalizedDebt);

    uint256 totalNormalizedDebtAfter = totalNormalizedDebt(i); 
    uint256 debtCeilingAfter = debtCeiling(i); 
    uint256 totalNormalizedDebtOtherAfter = totalNormalizedDebt(otherIlk); 
    uint256 collateralAfter = collateral(i, u); 
    uint256 normalizedDebtAfter = normalizedDebt(i, u);
    uint256 normalizedDebtOtherAfter = normalizedDebt(otherIlkU, otherUsrU);
    uint256 gemAfter = gem(i, v);
    uint256 gemOtherAfter = gem(otherIlkV, otherUsrV);
    uint256 unbackedDebtAfter = unbackedDebt(w);
    uint256 unbackedDebtOtherAfter = unbackedDebt(otherUsrW);
    uint256 totalUnbackedDebtAfter = totalUnbackedDebt();

    assert(to_mathint(totalNormalizedDebtAfter) == to_mathint(totalNormalizedDebtBefore) + to_mathint(changeInNormalizedDebt), "grab did not set ilks[i].Art");
    assert(totalNormalizedDebtOtherAfter == totalNormalizedDebtOtherBefore, "grab did not keep unchanged the rest of ilks[x].Art");
    assert(to_mathint(collateralAfter) == to_mathint(collateralBefore) + to_mathint(changeInCollateral), "grab did not set urns[u].ink");
    assert(to_mathint(normalizedDebtAfter) == to_mathint(normalizedDebtBefore) + to_mathint(changeInNormalizedDebt), "grab did not set urns[u].normalizedDebt");
    assert(normalizedDebtOtherAfter == normalizedDebtOtherBefore, "grab did not keep unchanged the rest of urns[x].art");
    assert(to_mathint(gemAfter) == to_mathint(gemBefore) - to_mathint(changeInCollateral), "grab did not set gem[i][v]");
    assert(gemOtherAfter == gemOtherBefore, "grab did not keep unchanged the rest of gem[x][y]");
    assert(to_mathint(unbackedDebtAfter) == to_mathint(unbackedDebtBefore) - to_mathint(rateBefore) * to_mathint(changeInNormalizedDebt), "grab did not set sin[w]");
    assert(unbackedDebtOtherAfter == unbackedDebtOtherBefore, "grab did not keep unchanged the rest of sin[x]");
    assert(to_mathint(totalUnbackedDebtAfter) == to_mathint(totalUnbackedDebtBefore) - to_mathint(rateBefore) * to_mathint(changeInNormalizedDebt), "grab did not set vice");
}

