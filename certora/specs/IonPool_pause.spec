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
    function rateUnaccrued(uint8) external  returns uint256 envfree;

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




// Verify correct storage changes for non reverting cage
rule pause() {
    env e;

    address anyUsr;  uint8 anyIlk;

    uint256 rateBefore = rateUnaccrued(e, anyIlk); 
    uint256 debtBefore = debt(e);
    uint256 ilkCount = ilkCount();
    require ilkCount < max_ilk();
    require debtBefore > 1;
    uint256 timeblockbefore = e.block.timestamp;

    pause(e);

    uint256 rateAfter = rateUnaccrued(e, anyIlk); 
    uint256 debtAfter = debt(e);
    uint256 timeblocafter = e.block.timestamp;


    assert(rateAfter == rateBefore, "cage did not keep unchanged every ilks[x].rate");
    assert(debtAfter > debtBefore, "Should accrue interest");
    assert(timeblocafter > timeblockbefore, "Time should pass");
}

