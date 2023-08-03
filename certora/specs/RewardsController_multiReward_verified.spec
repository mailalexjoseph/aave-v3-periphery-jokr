import "methods/Methods_base.spec";
// use invariant totalSupply_eq_sumAllBalanceAToken;

///////////////// Properties ///////////////////////




// STAUS: VERIFIED
rule handleAction_unit_test_multi() {
    env e;
    address user;
    uint256 totalSupply;
    uint256 userBalance;
    address asset  = e.msg.sender;
    address reward = getNthRewardByAsset(e.msg.sender,2);

    requireInvariant totalSupply_eq_sumAllBalanceAToken();
    require getAvailableRewardsCount(asset) == 2;
    uint256 oldIndex ; uint256 newIndex;
    oldIndex,newIndex = getAssetIndex(e,asset,reward);
    userBalance,totalSupply = AToken.getScaledUserBalanceAndSupply(e,user);

    uint256 _accruedRewards = getUserAccruedRewardsForAsset(user,asset,reward);
    uint256 rewards         = getRewards(user,asset,reward,userBalance,newIndex);

    handleAction(e,user,totalSupply,userBalance);

    uint256 accruedRewards_ = getUserAccruedRewardsForAsset(user,asset,reward);

    assert getCurrentRewardIndex(asset,reward) == newIndex,
        "Incorrect reward index update";
    assert getUserAssetIndex(user,asset,reward) == newIndex,
        "Incorrect user index update";
    assert getlastUpdateTimestamp(asset,reward) == e.block.timestamp,
        "Incorrect lastUpdateTimestamp";
    assert to_mathint(accruedRewards_) == _accruedRewards + rewards,
        "accruedRewards changed by wrong amount";

}