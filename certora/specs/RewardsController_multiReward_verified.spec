import "methods/Methods_base.spec";
use invariant totalSupply_eq_sumAllBalanceAToken;

///////////////// Properties ///////////////////////




// STAUS: VERIFIED
rule handleAction_unit_test_multi() {
    env e;
    address user;
    uint256 totalSupply;
    uint256 userBalance;
    address asset  = e.msg.sender;
    address reward = getNthRewardByAsset(e.msg.sender,1);

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



// STATUS: SANITY FAILED 
// Need to figure out why sanity checks are failing for loops with multiple iterations
// Need to contact michael
rule claimAllRewards_unit_test_multi(address asset1,address asset2,address to) {
    env e;
    address[] assets = [asset1,asset2];

    require getAvailableRewardsCount(asset1) == 0;
    require getAvailableRewardsCount(asset2) == 2;
    address[] availableRewards2 = getRewardsByAsset(asset2);

    address[] rewardList = getRewardsList();
    require getRewardsListLength() == 2;

    require availableRewards2[0] == rewardList[0];
    require availableRewards2[1] == rewardList[1];

    require getRewardsListLength() == 2;
    require availableRewards2[0] == rewardList[0];
    require availableRewards2[0] == rewardList[1];

    require rewardList[0] != rewardList[1];

    address reward = rewardList[1];

    uint256 rewards = getUserRewards(e,assets,e.msg.sender,reward);

    address[] rewardListOutput ; uint256[] claimedAmounts;
    rewardListOutput,claimedAmounts = claimAllRewards(e,assets,to);

    uint256 accruedRewards_ = getUserAccruedRewardsForAsset(e.msg.sender,asset2,reward);

    assert accruedRewards_ == 0,
        "Accrued rewards must be zero after claiming all rewards"; 
    assert claimedAmounts[0] == rewards,
        "Incorrect claimedAmounts";
    assert getlastUpdateTimestamp(asset2,reward) == e.block.timestamp,
        "Incorrect lastUpdateTimestamp";
}



// STATUS: TIMEOUT
rule claimRewardsMultiple (
    env e,
    address asset1,
    address asset2,
    uint256 amount,
    address to
) { 
    address[] assets = [asset1, asset2];

    address[] availableRewards1 = getRewardsByAsset(asset1);
    require getAvailableRewardsCount(asset1) == 1;

    address[] availableRewards2 = getRewardsByAsset(asset2);
    require getAvailableRewardsCount(asset2) == 1;

    require availableRewards1[0] == availableRewards2[0];

    uint256 userRewardsBefore = getUserRewards(e, assets, e.msg.sender, availableRewards1[0]);
        
    uint256 expectedRewards = claimRewards(e, assets, amount, to, availableRewards1[0]);

    uint256 userRewardsAfter = getUserRewards(e, assets, e.msg.sender, availableRewards1[0]);


    assert  amount == 0 => expectedRewards == 0;

    assert amount != 0 && amount < userRewardsBefore =>
        expectedRewards == amount &&
        userRewardsAfter == assert_uint256(userRewardsBefore - amount);

    assert amount != 0 && amount >= userRewardsBefore => 
        expectedRewards == userRewardsBefore &&
        userRewardsAfter == 0;

}