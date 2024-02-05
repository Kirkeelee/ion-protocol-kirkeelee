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


invariant ilkCountisEqualtoOrLessthanMaxIlk()
          ilkCount() <= 256;


// Verify correct storage changes for non reverting rely
rule addOperator(address usr) {
    env e;

    address other;
    address operator;
    require(other != usr);
    require(operator != usr);
    
    bool wardsOtherBefore = isOperator(other, operator);
    
    
    addOperator(e, usr);

    bool wardsAfter = isOperator(e.msg.sender, usr);
    bool wardsOtherAfter = isOperator(other, operator);
    
    
    assert(wardsAfter == true, "rely did not set wards");
    assert(wardsOtherAfter == wardsOtherBefore, "rely did not keep unchanged the rest of wards[x]");
    
}



// Verify correct storage changes for non reverting deny
rule removeOperator(address operator) {
    env e;

    address other;
    require(other != e.msg.sender);
    
    bool wardsOtherBefore = isOperator(other, operator);
    
    removeOperator(e, operator);

    bool wardsAfter = isOperator(e.msg.sender, operator);
    bool wardsOtherAfter = isOperator(other, operator);
    
    
    assert(wardsAfter == false, "deny did not set wards");
    assert(wardsOtherAfter == wardsOtherBefore, "deny did not keep unchanged the rest of wards[x]");
    
}



// Verify correct storage changes for non reverting init
rule initializeIlk(address IlkAddress) {
    env e;
    storage init = lastStorage;

    requireInvariant ilkCountisEqualtoOrLessthanMaxIlk();
    
    uint8 otherIlk; 
    uint256 rateotherIlkBefore = rateUnaccrued(e, otherIlk);
    bool addressContainsbefore = addressContains(IlkAddress);
    require addressContainsbefore == false;
     
        
    initializeIlk(e, IlkAddress);
        
    uint8 ilk = getIlkIndex(e, IlkAddress); 
    uint256 rateAfter = rateUnaccrued(e, ilk);
    bool addressContains = addressContains(IlkAddress);
    address getIlkAddress = getIlkAddress(ilk);
    uint256 rateotherIlkAfter = rateUnaccrued(e, otherIlk);
    uint256 lastRateUpdate = lastRateUpdate(ilk);
    uint256 dustAfter = dust(ilk);
    uint256 totalNormalizedDebt = totalNormalizedDebt(ilk);
    require lastRateUpdate == e.block.timestamp;

    require ilk != otherIlk;

    
    assert(addressContains == true, "should register");
    assert(rateotherIlkBefore == rateotherIlkAfter, "should not affect other ilks");
    assert(lastRateUpdate == e.block.timestamp, "init did not set ilks[ilk].lastRateUpdate");
    assert(rateAfter == RAY(), "init did not set ilks[ilk].rate");
    assert(dustAfter == 0, "init did not set ilks[ilk].rate");
    assert(totalNormalizedDebt == 0, "should be 0");
    assert(getIlkAddress == IlkAddress, "Should get the same address");


}



// Verify revert rules on init
rule initializeIlk_revert(address ilk) {
    env e;
    uint8 anyIlk;
    uint256 ilkCount = ilkCount();
    address zero_address = 0;
    bool alreadyAdded = addressContains(ilk);

    initializeIlk@withrevert(e, ilk);

    bool revert1 = ilk == zero_address;
    bool revert2 = alreadyAdded == true; //ilk aready exists.
    bool revert3 = ilkCount >= max_ilk();

    assert(revert1 => lastReverted, "revert1 failed");
    assert(revert2 => lastReverted, "revert2 failed");
    assert(revert3 => lastReverted, "revert3 failed");

}

// Verify correct storage changes for non reverting cage
rule pause() {
    env e;

    uint8 anyIlk;
    uint256 rateBefore = rateUnaccrued(e, anyIlk); 
    uint256 debtBefore = debtUnaccrued(e);
    uint256 ilkCount = ilkCount();
    uint256 lastRateUpdate = lastRateUpdate(anyIlk);
    require ilkCount !=0;
    require debtBefore !=0;
    require lastRateUpdate < e.block.timestamp;

    pause(e);

    uint256 rateAfter = rateUnaccrued(e, anyIlk); 
    uint256 debtAfter = debtUnaccrued(e);

    assert(rateAfter >= rateBefore, "cage did not keep unchanged every ilks[x].rate");
    assert(debtAfter >= debtBefore, "Should accrue interest");
}



rule vault_getters() {
    uint8 ilk; address vault;
    uint256 collateral = collateral(ilk, vault);
    uint256 normalizedDebt= normalizedDebt(ilk, vault);
    collateral, normalizedDebt = vault(ilk, vault);

    assert(collateral == collateral(ilk, vault), "ink getter did not return urns.ink");
    assert(normalizedDebt == normalizedDebt(ilk, vault), "art getter did not return urns.art");
}

// Verify correct storage changes for non reverting slip
rule mintAndBurnGem(uint8 ilk, address usr, int256 wad) {
    env e;

    uint8 otherIlk; address otherUsr; 
    require(otherIlk != ilk || otherUsr != usr);
    
    uint256 gemBefore = gem(ilk, usr);
    uint256 gemOtherBefore = gem(otherIlk, otherUsr);
    
    mintAndBurnGem(e, ilk, usr, wad);

   
    uint256 gemAfter = gem(ilk, usr);
    uint256 gemOtherAfter = gem(otherIlk, otherUsr);
    
    
    assert(to_mathint(gemAfter) == to_mathint(gemBefore) + to_mathint(wad), "slip did not set gem[ilk][usr]");
    assert(gemOtherAfter == gemOtherBefore, "slip did not keep unchanged the rest of gem[x][y]");
   
}



// Verify correct storage changes for non reverting flux
rule transferGem(uint8 ilk, address src, address dst, uint256 wad) {
    env e;

    uint8 otherIlk; address otherUsr; 
    require(otherIlk != ilk || (otherUsr != src && otherUsr != dst));
    
    
    uint256 gemSrcBefore = gem(ilk, src);
    uint256 gemDstBefore = gem(ilk, dst);
    uint256 gemOtherBefore = gem(otherIlk, otherUsr);
    
    transferGem(e, ilk, src, dst, wad);

    
    uint256 gemSrcAfter = gem(ilk, src);
    uint256 gemDstAfter = gem(ilk, dst);
    uint256 gemOtherAfter = gem(otherIlk, otherUsr);
    
    
    assert(src != dst => to_mathint(gemSrcAfter) == to_mathint(gemSrcBefore - wad), "flux did not set gem[ilk][src]");
    assert(src != dst => to_mathint(gemDstAfter) == to_mathint(gemDstBefore + wad), "flux did not set gem[ilk][dst]");
    assert(src == dst => gemSrcAfter == gemDstBefore, "flux did not keep unchanged gem[ilk][src/dst]");
    assert(gemOtherAfter == gemOtherBefore, "flux did not keep unchanged the rest of gem[x][y]");
    
}

// Verify revert rules on flux
rule transferGem_revert(uint8 ilk, address src, address dst, uint256 wad) {
    env e;

    bool isAllowed = isAllowed(src, e.msg.sender) == true;
    uint256 gemSrc = gem(ilk, src);
    uint256 gemDst = gem(ilk, dst);

    transferGem@withrevert(e, ilk, src, dst, wad);

    bool revert2 = !isAllowed;
    bool revert3 = gemSrc < wad;
    bool revert4 = src != dst && gemDst + wad > max_uint256;

    assert(revert2 => lastReverted, "revert2 failed");
    assert(revert3 => lastReverted, "revert3 failed");
    assert(revert4 => lastReverted, "revert4 failed");

}

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
    uint256 rateAfter = rateUnaccrued(e, i);
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
    assert(to_mathint(unbackedDebtAfter) == to_mathint(unbackedDebtBefore) - to_mathint(rateAfter) * to_mathint(changeInNormalizedDebt), "grab did not set sin[w]");
    assert(unbackedDebtOtherAfter == unbackedDebtOtherBefore, "grab did not keep unchanged the rest of sin[x]");
    assert(to_mathint(totalUnbackedDebtAfter) == to_mathint(totalUnbackedDebtBefore) - to_mathint(rateAfter) * to_mathint(changeInNormalizedDebt), "grab did not set vice");
}



// Verify correct storage changes for non reverting heal
rule repayBadDebt(address user, uint256 rad) {
    env e;

    address otherUsr;
    require(otherUsr != user);

    
    uint256 unbackedDebtSenderBefore = unbackedDebt(user);
    uint256 unbackedDebtOtherBefore = unbackedDebt(otherUsr);
    uint256 debtBefore = debtUnaccrued(e);
    uint256 totalUnbackedDebtBefore = totalUnbackedDebt();

    repayBadDebt(e, user, rad);

    uint256 unbackedDebtSenderAfter = unbackedDebt(user);
    uint256 unbackedDebtOtherAfter = unbackedDebt(otherUsr);
    uint256 debtAfter = debtUnaccrued(e);
    uint256 totalUnbackedDebtAfter = totalUnbackedDebt();

    assert(to_mathint(unbackedDebtSenderAfter) == to_mathint(unbackedDebtSenderBefore - rad), "heal did not set sin[sender]");
    assert(unbackedDebtOtherAfter == unbackedDebtOtherBefore, "heal did not keep unchanged the rest of sin[x]");
    assert(to_mathint(debtAfter) == to_mathint(debtBefore - rad), "heal did not set debt");
    assert(to_mathint(totalUnbackedDebtAfter) == to_mathint(totalUnbackedDebtBefore - rad), "heal did not set vice");
} 


