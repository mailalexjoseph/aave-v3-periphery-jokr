import "methods/Methods_base.spec";
import "RewardsController_base.spec";
use invariant user_index_LEQ_index;

/**************************************************
*                 DEFINITIONS                     *
**************************************************/
definition isConfigureAssets(method f) returns bool = 
    f.selector == sig:configureAssets(RewardsDataTypes.RewardsConfigInput[]).selector;


/**************************************************
*                 INVARIANTS                      *
**************************************************/

invariant totalSupply_eq_sumAllBalanceAToken()
    to_mathint(AToken.totalSupply()) == sumAllBalanceAToken();



// STATUS: VERIFIED
// Property: index lastUpdateTime cannot surpass block.timestamp
invariant update_time_LEQ_block_time(env e,address asset,address reward)
    getlastUpdateTimestamp(asset,reward) <= e.block.timestamp
    {
        preserved with(env e1) {
            require e.block.timestamp == e1.block.timestamp;
        }
    }


// STATUS: VERIFIED
// Property: There is no way to claim rewards to zero address
invariant zero_address_has_no_rewards(env e) 
    Reward.balanceOf(e,0) == 0
    {
       preserved with(env e1) {
            require e1.msg.sender != 0;
        }
    }


// STATUS: TIMEOUT
invariant user_rewards_LEQ_emissions_till_now(env e, address user, address asset, address reward)
    to_mathint(getAllUserRewards(e,user,asset,reward)) <= 
    (getCurrentRewardIndex(asset,reward) * AToken.scaledTotalSupply(e))/ (10 ^ getAssetDecimals(asset))
    {
        preserved {
            requireInvariant totalSupply_eq_sumAllBalanceAToken();
        }
        preserved handleAction(address user1,uint256 totalSupply,uint256 userBalance) with(env e1) {
            require e1.block.timestamp == e.block.timestamp;
            uint256 userBalance1; uint256 totalSupply1;
            userBalance1,totalSupply1 = AToken.getScaledUserBalanceAndSupply(e,user1);
            require totalSupply == totalSupply1 && userBalance == userBalance1;
        }
    }

/**************************************************
*                   UNIT TESTS                    *
**************************************************/


// STAUS: VERIFIED
rule handleActionUnitTest(method f) filtered { f -> !f.isView } {
    env e;
    address user;
    uint256 totalSupply;
    uint256 userBalance;
    address asset  = e.msg.sender;
    address reward = getNthRewardByAsset(e.msg.sender,1);

    requireInvariant totalSupply_eq_sumAllBalanceAToken();
    require getAvailableRewardsCount(asset) == 1;
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

// STATUS: NOT VERIFIED
// Property: configureAssets is behaving as expected
// rule configureAssets_unit_test(method f) {
//     RewardsDataTypes.RewardsConfigInput[] rewardsInput;
//     // require rewardsInput.length == 1;
//     // configureAssets(e,rewardList);

//     // assert getTransferStrategy(rewardsInput[0].reward) == rewardsInput[0].transferStrategy,
//     //     "transferStrategy not updated correctly";
    
//     // assert getRewardOracle(rewardsInput[0].reward) == rewardsInput[0].transferStrategy.rewardOracle,
//     //     "rewardOracle not updated correctly";


// }


// STATUS: VERIFIED
rule claimAllRewardsUnitTest(address asset,address to,method f)  filtered { f -> !f.isView } {
    env e;
    address[] assets = [asset];

    address[] availableRewards = getRewardsByAsset(asset);
    require getAvailableRewardsCount(asset) == 1;

    address[] rewardList = getRewardsList();
    require getRewardListLength() == 1;

    require availableRewards[0] == rewardList[0];

    requireInvariant totalSupply_eq_sumAllBalanceAToken();

    claimAllRewards(e,assets,to);

    assert getUserAccruedRewardsForAsset(e.msg.sender,asset,availableRewards[0]) == 0,
        "Accrued rewards must be zero after claiming all rewards"; 
    
}

// Rules - ClaimRewards unit tests
rule claimRewardSingle (
    env e,
    address asset,
    uint256 amount,
    address to
) {
    
    address[] assets = [asset];

    address[] availableRewards = getRewardsByAsset(asset);
    require getAvailableRewardsCount(asset) == 1;

    uint256 userRewardsBefore = getUserRewards(e, assets, e.msg.sender, availableRewards[0]);
    
    uint256 expectedRewards = claimRewards(e, assets, amount, to, availableRewards[0]);

    uint256 userRewardsAfter = getUserAccruedRewardsForAsset(e.msg.sender, assets[0], availableRewards[0]);

    assert amount == 0 => expectedRewards == 0;

    assert amount != 0 && userRewardsBefore <= amount =>
        expectedRewards == userRewardsBefore &&
        userRewardsAfter == 0;

    assert amount != 0 && userRewardsBefore > amount =>
        expectedRewards == amount &&
        userRewardsAfter == assert_uint256(userRewardsBefore - amount);

}

// STATUS: TIMEOUT
rule claimRewardMultiple (
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

/**************************************************
*               REVERT CONDITIONS                 *
**************************************************/

// STATUS: VERIFIED
// Property: claimAllRewards function should revert when to address is zero
rule claimAllRewards_should_revert(address[] assets,address to, method f) filtered { f -> !f.isView } {
    env e;
    claimAllRewards@withrevert(e,assets,to);
    assert to == 0 => lastReverted,
        "claimAllRewards should revert when to address is zero";
} 


// STATUS: VERIFIED
// Property: claimAllRewards function should revert when to address is zero
rule claimAllRewardsOnBehalf_should_revert(address[] assets, address user, address to, method f) filtered { f -> !f.isView } {
    env e;
    claimAllRewardsOnBehalf@withrevert(e,assets,user,to);
    assert user == 0 || to == 0 => lastReverted,
        "claimAllRewardsOnBehalf should revert when to address or user address is zero";
} 

// STATUS: VERIFIED
// Property: claimRewards function should revert when to address is zero
rule claimRewards_should_revert(address[] assets, uint256 amount, address to, address reward, method f) filtered { f -> !f.isView } {
    env e;
    claimRewards@withrevert(e,assets,amount,to,reward);
    assert to == 0 => lastReverted,
        "claimRewards should revert when to address is zero";

}

// STATUS: VERIFIED
// Property: claimRewardsOnBehalf should revert when to address is zero
rule claimRewardsOnBehalf_should_revert(address[] assets, uint256 amount, address user, address to, address reward,  method f) filtered { f -> !f.isView } {
    env e;
    claimRewardsOnBehalf@withrevert(e,assets,amount,user,to,reward);
    assert user == 0 || to == 0 => lastReverted,
        "claimRewardsOnBehalf should revert when to address or user address is zero";
} 



/**************************************************
*                VARIABLE CHANGES                 *
**************************************************/

// claimRewardsToSelf should only change rewards of msg.sender

// system properties like emissionsPerSecond and distributionEnd should only changed by emissionsManager

// emissionManager function can only be called by emissionManager




/**************************************************
*             HIGH LEVEL PROPERTIES               *
**************************************************/

// STATUS: NOT VERIFIED
// Property: rewards of user should always be less than total emissions
// Idea:getRewards(user) <= emissionsPerSecond * endTime - initiatedTime 
// rule user_rewards_LEQ_emissions()


// STATUS: NOT VERIFIED
// Property: a user should get all rewards if he owns the whole totalSupply in the emissionsPeriod
// Idea : configureAsset and makesure 


// STATUS : VERIFIED
// Property: Rewards of a user for a particular asset dont increase after distribution End
rule rewards_wont_increase_after_distribution_end(address user, address asset, address reward, method f) filtered { f -> !f.isView } {
    requireInvariant user_index_LEQ_index(asset,reward,user);
    requireInvariant totalSupply_eq_sumAllBalanceAToken();

    env e; calldataarg args; 
    uint _end     =  getDistributionEnd(asset,reward);
    uint _rewards = getAllUserRewards(e,user,asset,reward);

    require e.block.timestamp > _end;

    if(f.selector == sig:handleAction(address,uint256,uint256).selector) {
        address user1;
        uint256 totalSupply;
        uint256 userBalance;
        userBalance,totalSupply = AToken.getScaledUserBalanceAndSupply(e,user1);
        handleAction(e,user1,totalSupply,userBalance);
    } else {
        f(e,args);  
    }   
   
    uint end_     = getDistributionEnd(asset,reward);
    uint rewards_ = getAllUserRewards(e,user,asset,reward);

    assert end_ == _end && !isConfigureAssets(f) => rewards_ <= _rewards;
}


// STATUS: VERIFIED
// Property: user index will never decrease
rule user_index_keeps_growing(address user,address asset, address reward, method f) filtered { f -> !f.isView } {

    requireInvariant user_index_LEQ_index(asset,reward,user);

    uint256 _index = getUserAssetIndex(user, asset, reward);

    env e; calldataarg args;
    f(e, args);

    uint256 index_ = getUserAssetIndex(user, asset, reward);
        
    assert index_ >= _index;
}

// STATUS: VERIFIED
// Property: last update timestamp should only increase
rule last_update_time_only_increases(address asset, address reward, method f) filtered {f -> !f.isView} {

    env e;
    calldataarg args;
    requireInvariant update_time_LEQ_block_time(e,asset,reward);

    uint _lastUpdateTimestamp = getlastUpdateTimestamp(asset,reward);

    f(e,args);

    uint lastUpdateTimestamp_ = getlastUpdateTimestamp(asset,reward);

    assert lastUpdateTimestamp_ >= _lastUpdateTimestamp;
}



