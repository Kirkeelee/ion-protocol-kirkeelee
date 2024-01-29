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
    uint8 otherIlk; 
    uint256 rateotherIlkBefore = rate(e, otherIlk);

    initializeIlk(e, IlkAddress);
        
    uint8 ilk = getIlkIndex(e, IlkAddress); 
    uint256 rateAfter = rate(e, ilk); 
    uint256 rateotherIlkAfter = rate(e, otherIlk);
    

    assert(rateotherIlkBefore == rateotherIlkAfter, "should not affect other ilks");
    assert(rateAfter == RAY(), "init did not set ilks[ilk].rate");

}

// Verify revert rules on init
rule initializeIlk_revert(address ilk) {
    env e;
    uint8 anyIlk;
    uint256 ilkCount = ilkCount();
    address zero_address = 0;
    address otherilkadd = getIlkAddress(anyIlk);

    initializeIlk@withrevert(e, ilk);

    bool revert1 = ilk == zero_address;
    bool revert2 = ilk == otherilkadd; //ilk aready exists.
    bool revert3 = ilkCount >= max_ilk();

    assert(revert1 => lastReverted, "revert1 failed");
    assert(revert2 => lastReverted, "revert2 failed");
    assert(revert3 => lastReverted, "revert3 failed");

    assert(lastReverted => revert1 || revert2 || revert3, "Revert rules are not covering all the cases");
}

// Verify correct storage changes for non reverting cage
rule pause() {
    env e;

    address anyUsr;  uint8 anyIlk;

    uint256 rateBefore = rate(e, anyIlk); 
    uint256 debtBefore = debt(e);

    pause(e);

    uint256 rateAfter = rate(e, anyIlk); 
    uint256 debtAfter = debt(e);

    assert(rateAfter == rateBefore, "cage did not keep unchanged every ilks[x].rate");
    assert(debtAfter > debtBefore, "Should accrue interest");
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

    assert(lastReverted => revert2 || revert3 || revert4, "Revert rules are not covering all the cases");
}
/*

// Verify correct storage changes for non reverting frob
rule frob(uint8 i, address u, address v, address w, int256 changeInCollateral, int256 changeInNormalizedDebt) {
    env e;

    uint8 otherIlk;
    require(otherIlk != i);
    uint8 otherIlkU; address otherUsrU;
    require(otherIlkU != i || otherUsrU != u);
    uint8 otherIlkV; address otherUsrV;
    require(otherIlkV != i || otherUsrV != v);
    address otherUsrW;
    require(otherUsrW != w);
    address anyUsr; address anyUsr2;

    uint256 wardsBefore = wards(anyUsr);
    uint256 canBefore = can(anyUsr, anyUsr2);
    uint256 totalNormalizedDebtBefore; uint256 rateBefore; uint256 spotBefore; uint256 debtCeilingBefore; uint256 dustBefore;
    totalNormalizedDebtBefore, rateBefore, spotBefore, debtCeilingBefore, dustBefore = ilks(i);
    uint256 ArtOtherBefore; uint256 rateOtherBefore; uint256 spotOtherBefore; uint256 debtCeilingOtherBefore; uint256 dustOtherBefore;
    ArtOtherBefore, rateOtherBefore, spotOtherBefore, debtCeilingOtherBefore, dustOtherBefore = ilks(otherIlk);
    uint256 collateralBefore; uint256 normalizedDebtBefore;
    collateralBefore, normalizedDebtBefore =vault(i, u);
    uint256 collateralOtherBefore; uint256 normalizedDebtOtherBefore;
    collateralOtherBefore, normalizedDebtOtherBefore =vault(otherIlkU, otherUsrU);
    uint256 gemBefore = gem(i, v);
    uint256 gemOtherBefore = gem(otherIlkV, otherUsrV);
    uint256 wethBefore = weth(w);
    uint256 wethOtherBefore = weth(otherUsrW);
    uint256 debtBefore = debt();
    uint256 unbackedDebtBefore = unbackedDebt(anyUsr);
    uint256 totalUnbackedDebtBefore = totalUnbackedDebt();
    uint256 wethSupplyCapBefore = wethSupplyCap();
    //uint256 liveBefore = live();

    frob(e, i, u, v, w, changeInCollateral, changeInNormalizedDebt);

    uint256 wardsAfter = wards(anyUsr);
    uint256 canAfter = can(anyUsr, anyUsr2);
    uint256 totalNormalizedDebtAfter; uint256 rateAfter; uint256 spotAfter; uint256 debtCeilingAfter; uint256 dustAfter;
    totalNormalizedDebtAfter, rateAfter, spotAfter, debtCeilingAfter, dustAfter = ilks(i);
    uint256 ArtOtherAfter; uint256 rateOtherAfter; uint256 spotOtherAfter; uint256 debtCeilingOtherAfter; uint256 dustOtherAfter;
    ArtOtherAfter, rateOtherAfter, spotOtherAfter, debtCeilingOtherAfter, dustOtherAfter = ilks(otherIlk);
    uint256 collateralAfter; uint256 normalizedDebtAfter;
    collateralAfter, normalizedDebtAfter =vault(i, u);
    uint256 collateralOtherAfter; uint256 normalizedDebtOtherAfter;
    collateralOtherAfter, normalizedDebtOtherAfter =vault(otherIlkU, otherUsrU);
    uint256 gemAfter = gem(i, v);
    uint256 gemOtherAfter = gem(otherIlkV, otherUsrV);
    uint256 wethAfter = weth(w);
    uint256 wethOtherAfter = weth(otherUsrW);
    uint256 debtAfter = debt();
    uint256 unbackedDebtAfter = unbackedDebt(anyUsr);
    uint256 totalUnbackedDebtAfter = totalUnbackedDebt();
    uint256 wethSupplyCapAfter = wethSupplyCap();
    //uint256 liveAfter = live();

    assert(wardsAfter == wardsBefore, "frob did not keep unchanged every wards[x]");
    assert(canAfter == canBefore, "frob did not keep unchanged every can[x][y]");
    assert(to_mathint(totalNormalizedDebtAfter) == to_mathint(totalNormalizedDebtBefore) + to_mathint(changeInNormalizedDebt), "frob did not set ilks[i].Art");
    assert(rateAfter == rateBefore, "frob did not keep unchanged ilks[i].rate");
    assert(spotAfter == spotBefore, "frob did not keep unchanged ilks[i].spot");
    assert(debtCeilingAfter == debtCeilingBefore, "frob did not keep unchanged ilks[i].line");
    assert(dustAfter == dustBefore, "frob did not keep unchanged ilks[i].dust");
    assert(ArtOtherAfter == ArtOtherBefore, "frob did not keep unchanged rest of ilks[x].Art");
    assert(rateOtherAfter == rateOtherBefore, "frob did not keep unchanged rest of ilks[x].rate");
    assert(spotOtherAfter == spotOtherBefore, "frob did not keep unchanged rest of ilks[x].spot");
    assert(debtCeilingOtherAfter == debtCeilingOtherBefore, "frob did not keep unchanged rest of ilks[x].line");
    assert(dustOtherAfter == dustOtherBefore, "frob did not keep unchanged rest of ilks[x].dust");
    assert(to_mathint(collateralAfter) == to_mathint(collateralBefore) + to_mathint(changeInCollateral), "frob did not set urns[u].ink");
    assert(to_mathint(normalizedDebtAfter) == to_mathint(normalizedDebtBefore) + to_mathint(changeInNormalizedDebt), "frob did not set urns[u].art");
    assert(collateralOtherAfter == collateralOtherBefore, "frob did not keep unchanged rest of urns[x].ink");
    assert(normalizedDebtOtherAfter == normalizedDebtOtherBefore, "frob did not keep unchanged rest of urns[x].art");
    assert(to_mathint(gemAfter) == to_mathint(gemBefore) - to_mathint(changeInCollateral), "frob did not set gem[i][v]");
    assert(gemOtherAfter == gemOtherBefore, "frob did not keep unchanged rest of gem[x][y]");
    assert(to_mathint(wethAfter) == to_mathint(wethBefore) + to_mathint(rateBefore) * to_mathint(changeInNormalizedDebt), "frob did not set weth[w]");
    assert(wethOtherAfter == wethOtherBefore, "frob did not keep unchanged rest of dai[x]");
    assert(unbackedDebtAfter == unbackedDebtBefore, "frob did not keep unchanged every sin[x]");
    assert(to_mathint(debtAfter) == to_mathint(debtBefore) + to_mathint(rateBefore) * to_mathint(changeInNormalizedDebt), "frob did not set debt");
    assert(totalUnbackedDebtAfter == totalUnbackedDebtBefore, "frob did not keep unchanged vice");
    assert(wethSupplyCapAfter == wethSupplyCapBefore, "frob did not keep unchanged Line");
    //assert(liveAfter == liveBefore, "frob did not keep unchanged live");
}

// Verify revert rules on frob
rule frob_revert(uint8 i, address u, address v, address w, int256 changeInCollateral, int256 changeInNormalizedDebt) {
    env e;

    //uint256 live = live();

    bool wishU = u == e.msg.sender || can(u, e.msg.sender) == 1;
    bool wishV = v == e.msg.sender || can(v, e.msg.sender) == 1;
    bool wishW = w == e.msg.sender || can(w, e.msg.sender) == 1;

    uint256 wethSupplyCap = wethSupplyCap();

    uint256 totalNormalizedDebt; uint256 rate; uint256 spot; uint256 debtCeiling; uint256 dust;
    totalNormalizedDebt, rate, spot, debtCeiling, dust = ilks(i);

    uint256 collateral; uint256 normalizedDebt;
    collateral, normalizedDebt =vault(i, u);

    uint256 gem = gem(i, v);
    uint256 weth= weth(w);
    uint256 debt = debt();

    mathint collateralFinal = to_mathint(collateral) + to_mathint(changeInCollateral);
    mathint normalizedDebtFinal = to_mathint(normalizedDebt) + to_mathint(changeInNormalizedDebt);
    mathint ArtFinal = to_mathint(totalNormalizedDebt) + to_mathint(changeInNormalizedDebt);
    mathint debtFinal = to_mathint(debt) + to_mathint(rate) * to_mathint(changeInNormalizedDebt);

    frob@withrevert(e, i, u, v, w, changeInCollateral, changeInNormalizedDebt);

    bool revert1  = e.msg.value > 0;
    /bool revert2  = live != 1;
    bool revert3  = rate == 0;
    bool revert4  = to_mathint(collateral) + to_mathint(changeInCollateral) < 0 || to_mathint(collateral) + to_mathint(changeInCollateral) > max_uint256;
    bool revert5  = to_mathint(normalizedDebt) + to_mathint(changeInNormalizedDebt) < 0 || to_mathint(normalizedDebt) + to_mathint(changeInNormalizedDebt) > max_uint256;
    bool revert6  = to_mathint(totalNormalizedDebt) + to_mathint(changeInNormalizedDebt) < 0 || to_mathint(totalNormalizedDebt) + to_mathint(changeInNormalizedDebt) > max_uint256;
    bool revert7  = rate > max_int256();
    bool revert8  = to_mathint(rate) * to_mathint(changeInNormalizedDebt) < min_int256() || to_mathint(rate) * to_mathint(changeInNormalizedDebt) > max_int256();
    bool revert9  = rate * normalizedDebtFinal > max_uint256;
    bool revert10 = to_mathint(debt) + to_mathint(rate) * to_mathint(changeInNormalizedDebt) < 0 || to_mathint(debt) + to_mathint(rate) * to_mathint(changeInNormalizedDebt) > max_uint256;
    bool revert11 = ArtFinal * rate > max_uint256;
    bool revert12 = changeInNormalizedDebt > 0 && (ArtFinal * rate > debtCeiling || debtFinal > wethSupplyCap);
    bool revert13 = collateralFinal * spot > max_uint256;
    bool revert14 = (changeInNormalizedDebt > 0 || changeInCollateral < 0) && rate * normalizedDebtFinal > collateralFinal * spot;
    bool revert15 = (changeInNormalizedDebt > 0 || changeInCollateral < 0) && !wishU;
    bool revert16 = changeInCollateral > 0 && !wishV;
    bool revert17 = changeInNormalizedDebt < 0 && !wishW;
    bool revert18 = normalizedDebtFinal > 0 && rate * normalizedDebtFinal < dust;
    bool revert19 = to_mathint(gem) - to_mathint(changeInCollateral) < 0 || to_mathint(gem) - to_mathint(changeInCollateral) > max_uint256;
    bool revert20 = to_mathint(weth) + to_mathint(rate) * to_mathint(changeInNormalizedDebt) < 0 || to_mathint(weth) + to_mathint(rate) * to_mathint(changeInNormalizedDebt) > max_uint256;

    assert(revert1  => lastReverted, "revert1 failed");
    assert(revert2  => lastReverted, "revert2 failed");
    assert(revert3  => lastReverted, "revert3 failed");
    assert(revert4  => lastReverted, "revert4 failed");
    assert(revert5  => lastReverted, "revert5 failed");
    assert(revert6  => lastReverted, "revert6 failed");
    assert(revert7  => lastReverted, "revert7 failed");
    assert(revert8  => lastReverted, "revert8 failed");
    assert(revert9  => lastReverted, "revert9 failed");
    assert(revert10 => lastReverted, "revert10 failed");
    assert(revert11 => lastReverted, "revert11 failed");
    assert(revert12 => lastReverted, "revert12 failed");
    assert(revert13 => lastReverted, "revert13 failed");
    assert(revert14 => lastReverted, "revert14 failed");
    assert(revert15 => lastReverted, "revert15 failed");
    assert(revert16 => lastReverted, "revert16 failed");
    assert(revert17 => lastReverted, "revert17 failed");
    assert(revert18 => lastReverted, "revert18 failed");
    assert(revert19 => lastReverted, "revert19 failed");
    assert(revert20 => lastReverted, "revert20 failed");

    assert(lastReverted => revert1  || revert2  || revert3  ||
                           revert4  || revert5  || revert6  ||
                           revert7  || revert8  || revert9  ||
                           revert10 || revert11 || revert12 ||
                           revert13 || revert14 || revert15 ||
                           revert16 || revert17 || revert18 ||
                           revert19 || revert20, "Revert rules are not covering all the cases");
}
*/

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
    uint256 rateBefore = rate(e, i);
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



// Verify correct storage changes for non reverting heal
rule repayBadDebt(address user, uint256 rad) {
    env e;

    address otherUsr;
    require(otherUsr != user);

    
    uint256 unbackedDebtSenderBefore = unbackedDebt(user);
    uint256 unbackedDebtOtherBefore = unbackedDebt(otherUsr);
    uint256 debtBefore = debt(e);
    uint256 totalUnbackedDebtBefore = totalUnbackedDebt();

    repayBadDebt(e, user, rad);

    uint256 unbackedDebtSenderAfter = unbackedDebt(user);
    uint256 unbackedDebtOtherAfter = unbackedDebt(otherUsr);
    uint256 debtAfter = debt(e);
    uint256 totalUnbackedDebtAfter = totalUnbackedDebt();

    assert(to_mathint(unbackedDebtSenderAfter) == to_mathint(unbackedDebtSenderBefore - rad), "heal did not set sin[sender]");
    assert(unbackedDebtOtherAfter == unbackedDebtOtherBefore, "heal did not keep unchanged the rest of sin[x]");
    assert(to_mathint(debtAfter) == to_mathint(debtBefore - rad), "heal did not set debt");
    assert(to_mathint(totalUnbackedDebtAfter) == to_mathint(totalUnbackedDebtBefore - rad), "heal did not set vice");
}

