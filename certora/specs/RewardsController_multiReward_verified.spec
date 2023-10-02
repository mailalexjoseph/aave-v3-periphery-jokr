import "methods/Methods_base.spec";
using TransferStrategyMultiRewardHarness as TransferStrategy;
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

// STATUS: VERIFIED
// Property: setEmissionPerSecond is behaving as expected
rule setEmissionPerSecond_multi_unit_test(address asset, address[] rewards, uint88[] newEmissionsPerSecond) {
    env e;
    require rewards.length == 2;

    address reward           = rewards[1];
    require getlastUpdateTimestamp(asset,reward) < e.block.timestamp;

    uint88 emissionPerSecond = newEmissionsPerSecond[1];
    uint256 oldIndex ; uint256 newIndex;
    oldIndex,newIndex = getAssetIndex(e,asset,reward);

    setEmissionPerSecond(e,asset,rewards,newEmissionsPerSecond);

    assert assert_uint88(getEmissionPerSecond(asset,reward)) == emissionPerSecond,
        "emissionsPerSecond not updated";

    assert getAssetDecimals(asset) != 0 && getlastUpdateTimestamp(asset,reward) != 0,
        "call should only pass if asset decimals and lastupdate timestamp are not zero";
    
    assert getCurrentRewardIndex(asset,reward) == newIndex,
        "Incorrect reward index update";

    assert rewards.length == newEmissionsPerSecond.length,
        "mismatched array lengths";
}


// STATUS: VERIFIED BUT MISSING A POSSIBLE VIOLATION
rule claimAllRewards_unit_test_multi(address asset1,address asset2,address to) {
    env e;
    address[] assets = [asset1,asset2];

    address[] availableRewards = getRewardsByAsset(asset2);
    require getAvailableRewardsCount(asset2) == 2;

    address[] rewardList = getRewardsList();
    require getRewardsListLength() == 2;

    address reward = rewardList[1];

    require availableRewards[0] == rewardList[0];
    require availableRewards[1] == rewardList[1];
    

    uint256 rewards = getUserRewards(e,assets,e.msg.sender,reward);

    address[] rewardListOutput ; uint256[] claimedAmounts;
    rewardListOutput,claimedAmounts = claimAllRewards(e,assets,to);

    address temp = rewardListOutput[1];

    uint256 accruedRewards_ = getUserAccruedRewardsForAsset(e.msg.sender,asset2,reward);

    assert accruedRewards_ == 0,
        "Accrued rewards must be zero after claiming all rewards"; 
    // assert rewardList[0] != rewardList[1] => claimedAmounts[1] == rewards,
    //     "Incorrect claimedAmounts";

}


// STATUS: TIMEOUT
rule claimAllRewards_should_update_index_data_multi(address asset1,address asset2,address to) {
    env e;
    address[] assets = [asset1,asset2];

    address[] availableRewards = getRewardsByAsset(asset2);
    require getAvailableRewardsCount(asset2) == 2;
    
    address[] rewardList = getRewardsList();
    require getRewardsListLength() == 2;

    address reward = rewardList[1];
    // simplifications
    address anyAsset;
    address anyReward;
    require getAssetDecimals(anyAsset) == 6;
    require getlastUpdateTimestamp(anyAsset,anyAsset) == e.block.timestamp;

    require availableRewards[0] == rewardList[0];
    require availableRewards[1] == rewardList[1];
    
    uint256 oldIndex ; uint256 newIndex;
    oldIndex,newIndex = getAssetIndex(e,asset2,reward);

    claimAllRewards(e,assets,to);

    assert getCurrentRewardIndex(asset2,reward) == newIndex,
        "Incorrect reward index update";
    assert getUserAssetIndex(e.msg.sender,asset2,reward) == newIndex,
        "Incorrect user index update";
    assert getlastUpdateTimestamp(asset2,reward) == e.block.timestamp,
        "Incorrect lastUpdateTimestamp";
}



// // STATUS: TIMEOUT
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

// STATUS: TIMEOUT
rule claimRewardsDividedMultiple (
    env e,
    address asset1,
    address asset2,
    uint256 amount,
    address to
) { 
    address[] assets = [asset1, asset2];
    address user = e.msg.sender;

    address[] availableRewards1 = getRewardsByAsset(asset1);
    require getAvailableRewardsCount(asset1) == 1;

    address[] availableRewards2 = getRewardsByAsset(asset2);
    require getAvailableRewardsCount(asset2) == 1;

    require availableRewards1[0] == availableRewards2[0];

    updateDataMultipleHarness(e, user, assets);

    uint256 asset1AccruedBefore = getUserAccruedRewardsForAsset(user, asset1, availableRewards1[0]);
    uint256 asset2AccruedBefore = getUserAccruedRewardsForAsset(user, asset2, availableRewards1[0]);
        
    uint256 expectedRewards = claimRewards(e, assets, amount, to, availableRewards1[0]);

    uint256 asset1AccruedAfter = getUserAccruedRewardsForAsset(user, asset1, availableRewards1[0]);
    uint256 asset2AccruedAfter = getUserAccruedRewardsForAsset(user, asset2, availableRewards1[0]);

    assert  amount == 0 => expectedRewards == 0;

    assert amount != 0 && amount < asset1AccruedBefore => asset1AccruedAfter == 0 && expectedRewards == amount;

}

// STATUS: NOT VERIFIED
// Property: ClaimAllRewards should increase the rewards balance of user
rule claimAllRewards_should_increase_reward_balance_multi(address asset1,address asset2,address to) {
    env e;
    address[] assets = [asset1,asset2];

    address[] availableRewards = getRewardsByAsset(asset2);
    require getAvailableRewardsCount(asset2) == 2;

    address[] rewardList = getRewardsList();
    require getRewardsListLength() == 2;

    address reward = rewardList[1];

    require availableRewards[0] == rewardList[0];
    require availableRewards[1] == rewardList[1];

    uint256 _balance = getRewardBalance(reward,to);

    address[] rewardListOutput ; uint256[] claimedAmounts;
    rewardListOutput,claimedAmounts = claimAllRewards(e,assets,to);

    uint256 balance_ = getRewardBalance(reward,to);

    assert to != TransferStrategy => to_mathint(balance_) >= _balance + claimedAmounts[1],
        "user rewards should increase after claimAllRewards";

}