import "methods/Methods_base.spec";
import "RewardsController_base.spec";
use invariant totalSupply_eq_sumAllBalanceAToken;
use invariant user_index_LEQ_index;
use rule index_keeps_growing;
use rule noDoubleClaim;
use rule onlyAuthorizeCanDecrease;

/**************************************************
*                 DEFINITIONS                     *
**************************************************/
definition isConfigureAssets(method f) returns bool = 
    f.selector == sig:configureAssets(RewardsDataTypes.RewardsConfigInput[]).selector;

definition isConfigureAssetsHarness(method f) returns bool =
    f.selector == sig:configureAssetsHarness(RewardsDataTypes.RewardsConfigInput,RewardsDataTypes.RewardsConfigInput).selector;

definition isClaimRewards(method f) returns bool =
    f.selector == sig:claimRewards(address[],uint256,address,address).selector;

definition isClaimRewardsOnBehalf(method f) returns bool =
    f.selector == sig:claimRewardsOnBehalf(address[],uint256,address,address,address).selector;

definition isClaimRewardsToSelf(method f) returns bool =
    f.selector == sig:claimRewardsToSelf(address[],uint256,address).selector;

definition isClaimAllRewards(method f) returns bool =
    f.selector == sig:claimAllRewards(address[],address).selector;

definition isClaimAllRewardsOnBehalf(method f) returns bool =
    f.selector == sig:claimAllRewardsOnBehalf(address[],address,address).selector;

definition isClaimAllRewardsToSelf(method f) returns bool =
    f.selector == sig:claimAllRewardsToSelf(address[]).selector;

definition isSetEmissionPerSecond(method f) returns bool =
    f.selector == sig:setEmissionPerSecond(address,address[],uint88[]).selector;

definition isSetDistributionEnd(method f) returns bool =
    f.selector == sig:setDistributionEnd(address,address,uint32).selector;

definition isHarnessMethod(method f) returns bool = isConfigureAssetsHarness(f);
 
definition claimMethods(method f) returns bool =
    isClaimRewards(f)    || isClaimRewardsOnBehalf(f)    || isClaimRewardsToSelf(f) ||
    isClaimAllRewards(f) || isClaimAllRewardsOnBehalf(f) || isClaimAllRewardsToSelf(f);


/**************************************************
*                 INVARIANTS                      *
**************************************************/




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
    getAllUserRewards(e,user,asset,reward) <= currentAvailableRewards(e,asset,reward)
    {
        preserved {
            requireInvariant totalSupply_eq_sumAllBalanceAToken();
            require getAssetDecimals(asset) == 6;
        }
        preserved handleAction(address user1,uint256 totalSupply,uint256 userBalance) with(env e1) {
            require e1.block.timestamp == e.block.timestamp;
            uint256 userBalance1; uint256 totalSupply1;
            userBalance1,totalSupply1 = AToken.getScaledUserBalanceAndSupply(e,user1);
            require totalSupply == totalSupply1 && userBalance == userBalance1;
        }
    }


// invariant user_owns_rewards_LEQ_emissions_till_now(env e, address user, address asset, address reward)
//     Reward.balanceOf(e,user) <= currentAvailableRewards(e,asset,reward)
//     {
//          preserved {
//             requireInvariant totalSupply_eq_sumAllBalanceAToken();
//         }
//         preserved handleAction(address user1,uint256 totalSupply,uint256 userBalance) with(env e1) {
//             require e1.block.timestamp == e.block.timestamp;
//             uint256 userBalance1; uint256 totalSupply1;
//             userBalance1,totalSupply1 = AToken.getScaledUserBalanceAndSupply(e,user1);
//             require totalSupply == totalSupply1 && userBalance == userBalance1;
//         }
//         preserved {

//         }

//     }


/**************************************************
*                   UNIT TESTS                    *
**************************************************/


// STAUS: VERIFIED
rule handleAction_unit_test(){
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

// STATUS: VERIFIED  
// Property: configureAssets is behaving as expected
// https://prover.certora.com/output/547/ac097c3a3288465684e99b4a93bb2463?anonymousKey=418a5e32f10d128fdb1ad038efc8c1c460de803f
rule configureAssets_unit_test(
    RewardsDataTypes.RewardsConfigInput rewardInput1,
    RewardsDataTypes.RewardsConfigInput rewardInput2
) {

    env e;
    require rewardInput1.reward != rewardInput2.reward;
    configureAssetsHarness(e,rewardInput1,rewardInput2);

    uint index ; uint emissionPerSecond;
    uint lastUpdateTimestamp; uint distributionEnd;

    index,emissionPerSecond,lastUpdateTimestamp,distributionEnd = getRewardsData(rewardInput1.asset,rewardInput1.reward);

    uint oldIndex ; uint newIndex;
    oldIndex,newIndex = getAssetIndex(e,rewardInput1.asset,rewardInput1.reward);


    assert getTransferStrategy(rewardInput1.reward) == rewardInput1.transferStrategy,
        "transferStrategy not updated";

    assert getTransferStrategy(rewardInput2.reward) == rewardInput2.transferStrategy,
        "transferStrategy not updated for second input";

    assert getRewardOracle(rewardInput1.reward) == rewardInput1.rewardOracle,
        "rewardOracle not updated";

    assert assert_uint88(emissionPerSecond) == rewardInput1.emissionPerSecond,
        "emissionsPerSecond not updated";
    
    assert lastUpdateTimestamp == e.block.timestamp,
        "lastUpdateTimestamp not updated";
    
    assert assert_uint32(distributionEnd) == rewardInput1.distributionEnd,
        "emissionsPerSecond not updated";

    assert index == newIndex,
        "index not updated";

}

// RULE: SANITY CHECK FAILED (LEAVE THIS RULE FOR 2 DAYS)
// Property: configureAssets functions adds assets and rewards to the lists
// https://prover.certora.com/output/547/c33eb8c226954f93b3baec82f83734e4?anonymousKey=367546d42a9ab3290c60f7873e52218d57d96ac4
// also check that available rewards are increased for the assets are increased and rewardEnabled set to true for both reward   
rule configureAssets_updates_assets_and_rewards_arrays(
    RewardsDataTypes.RewardsConfigInput rewardInput1,
    RewardsDataTypes.RewardsConfigInput rewardInput2
) { 
    env e;
    // require getAssetsListLength()  == 0;
    // require getRewardsListLength() == 0;

    // require rewardInput1.asset  != rewardInput2.asset;
    // require rewardInput1.reward != rewardInput2.reward;

    configureAssetsHarness(e,rewardInput1,rewardInput2);

    // address[] rewardList = getRewardsList();
    // address[] assetList  = getAssetsList(); 

    // assert rewardList[0] == rewardInput1.reward && rewardList[1] == rewardInput2.reward,
    //     "new rewards are not pushed into rewardList array";

    // assert assetList[0] == rewardInput1.asset && assetList[1] == rewardInput2.asset,
    //     "new assets are not pushed into assetList array";

    assert false;

// 
}


// STATUS: VERIFIED
rule claimAllRewardsUnitTest(address asset,address to) {
    env e;
    address[] assets = [asset];

    address[] availableRewards = getRewardsByAsset(asset);
    require getAvailableRewardsCount(asset) == 1;

    address[] rewardList = getRewardsList();
    require getRewardsListLength() == 1;

    require availableRewards[0] == rewardList[0];

    requireInvariant totalSupply_eq_sumAllBalanceAToken();
    require getAvailableRewardsCount(asset) == 1;
    require getRewardsListLength() == 1;
    require availableRewards[0] == rewardList[0];

    claimAllRewards(e,assets,to);

    assert getUserAccruedRewardsForAsset(e.msg.sender,asset,availableRewards[0]) == 0,
        "Accrued rewards must be zero after claiming all rewards"; 
    
}

// Rules - ClaimRewards unit tests
rule claimRewardsSingle (
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

rule claimRewardsShouldTransferRewards (
    env e,
    address asset,
    uint256 amount,
    address to
) {
    
    address[] assets = [asset];

    address[] availableRewards = getRewardsByAsset(asset);
    require getAvailableRewardsCount(asset) == 1;
    address transferStrategy = getTransferStrategy(availableRewards[0]);
    require transferStrategy != to;

    uint256 userRewardsBefore = getUserRewards(e, assets, e.msg.sender, availableRewards[0]);
    uint256 userBalanceBefore = getRewardBalance(availableRewards[0], to);
    uint256 vaultBalanceBefore = getRewardBalance(transferStrategy, to);
    
    
    uint256 expectedRewards = claimRewards(e, assets, amount, to, availableRewards[0]);

    uint256 userRewardsAfter = getUserAccruedRewardsForAsset(e.msg.sender, assets[0], availableRewards[0]);
    uint256 userBalanceAfter = getRewardBalance(availableRewards[0], to);
    uint256 vaultBalanceAfter = getRewardBalance(transferStrategy, to);

    assert amount == 0 => expectedRewards == 0;

    assert amount != 0 =>
        userBalanceAfter == assert_uint256(userBalanceBefore + expectedRewards) &&
        vaultBalanceAfter == assert_uint256(vaultBalanceBefore - expectedRewards);

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

rule setTransferStrategyUnitTest(address reward, address transferStrategy) {
    setTransferStrategy(reward, transferStrategy);
    assert getTransferStrategy(reward) == transferStrategy;
}

rule setRewardOracleUnitTest(address reward, address rewardOracle) {
    setRewardOracle(reward, rewardOracle);
    assert getRewardOracle(reward) == rewardOracle;
}

rule setClaimerUnitTest(address user, address caller) {
    setClaimer(user, caller);
    assert getClaimer(user) == caller;
}


/**************************************************
*               REVERT CONDITIONS                 *
**************************************************/

// STATUS: VERIFIED
// Property: claimAllRewards function should revert when to address is zero
rule claimAllRewards_should_revert(address[] assets,address to) {
    env e;
    claimAllRewards@withrevert(e,assets,to);
    assert to == 0 => lastReverted,
        "claimAllRewards should revert when to address is zero";
} 


// STATUS: VERIFIED
// Property: claimAllRewards function should revert when to address is zero
rule claimAllRewardsOnBehalf_should_revert(address[] assets, address user, address to) {
    env e;
    claimAllRewardsOnBehalf@withrevert(e,assets,user,to);
    assert user == 0 || to == 0 => lastReverted,
        "claimAllRewardsOnBehalf should revert when to address or user address is zero";
} 

// STATUS: VERIFIED
// Property: claimRewards function should revert when to address is zero
rule claimRewards_should_revert(address[] assets, uint256 amount, address to, address reward) {
    env e;
    claimRewards@withrevert(e,assets,amount,to,reward);
    assert to == 0 => lastReverted,
        "claimRewards should revert when to address is zero";

}

// STATUS: VERIFIED
// Property: claimRewardsOnBehalf should revert when to address is zero
rule claimRewardsOnBehalf_should_revert(address[] assets, uint256 amount, address user, address to, address reward) {
    env e;
    claimRewardsOnBehalf@withrevert(e,assets,amount,user,to,reward);
    assert user == 0 || to == 0 => lastReverted,
        "claimRewardsOnBehalf should revert when to address or user address is zero";
} 

rule setTransferStrategy_should_revert(address reward, address transferStrategy) {
    setTransferStrategy@withrevert(reward, transferStrategy);
    bool setTransferStrategyReverted = lastReverted;
    assert transferStrategy == 0 || !isContract(transferStrategy) => setTransferStrategyReverted,
        "transferStrategy should never be zero address";        
}

rule setRewardOracle_should_revert(address reward, address rewardOracle) {
    setRewardOracle@withrevert(reward, rewardOracle);
    bool setRewardOracleReverted = lastReverted;
    assert getLatestAnswer(rewardOracle) <= 0 => setRewardOracleReverted,
        "oracle must return price";
}

/**************************************************
*                VARIABLE CHANGES                 *
**************************************************/


// STATUS: VERIFIED
// Property: system properties like emissionsPerSecond and distributionEnd should only changed by emissionsManager
rule only_emission_manager_can_change(address asset,address reward,method f) filtered { f -> !f.isView && !isHarnessMethod(f) } {
    env e; calldataarg args;   

    uint _emissionPerSecond = getEmissionPerSecond(asset,reward);
    uint _end               = getDistributionEnd(asset,reward);

    f(e,args);

    uint emissionPerSecond_ = getEmissionPerSecond(asset,reward);
    uint end_               = getDistributionEnd(asset,reward);

    assert emissionPerSecond_ != _emissionPerSecond 
        => e.msg.sender == getEmissionManager() && 
        (isSetEmissionPerSecond(f) || isConfigureAssets(f)),
        "emissionPerSecond should only change in few functions by owner";

    assert end_ != _end => e.msg.sender == getEmissionManager() &&
        (isSetDistributionEnd(f) || isConfigureAssets(f)),
        "distributionEnd should only change in few functions by owner";
    
}


// STATUS: VERIFIED
// Property: claim functions should only decrease accrued rewards of a user
rule only_claim_functions_can_decrease_accrued_rewards(address user,address reward,method f) filtered { f -> !f.isView } {
    
    env e; calldataarg args;

    uint _accrued = getUserAccruedRewards(user,reward);

    f(e,args);

    uint accrued_ = getUserAccruedRewards(user,reward);

    assert accrued_ < _accrued => claimMethods(f),
        "only claim method should decrease user accrued rewards";

}





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


// STATUS: NOT VERIFIED
// Property: there shouldn't be a way where user has rewards but still get 0 rewards if tries to withdraw

// STATUS: VERIFIED 
// Property: claimedAmount should always be less than accrued rewards
rule claimed_amount_LEQ_accured_rewards(address asset, uint256 amount, address to) {
    env e;
    address[] assets = [asset];
    address[] availableRewards = getRewardsByAsset(asset);
    address[] rewardList = getRewardsList();

    require getAvailableRewardsCount(asset) == 1;
    require getRewardsListLength() == 1;
    require availableRewards[0] == rewardList[0];
    
    uint256 accruedRewards = getUserRewards(e,assets,e.msg.sender,availableRewards[0]);

    uint256 claimedAmount  = claimRewards(e,assets,amount,to,rewardList[0]);

    assert claimedAmount <= accruedRewards ,
        "claimedAmount should be less than accruedRewards";

}



// STATUS : VERIFIED
// Property: Rewards of a user for a particular asset dont increase after distribution End
rule rewards_wont_increase_after_distribution_end(address user, address asset, address reward, method f) filtered { f -> !f.isView && !isHarnessMethod(f) } {
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


/**************************************************
*            MATHEMATICAL PROPERTIES              *
**************************************************/

// STATUS: NOT VERIFIED
// Property: Anti-monotonicity of user Rewards balance and accrued rewards

// STATUS: 



/**************************************************
*                 RISK ANALYSIS                   *
**************************************************/

// STATUS: VERIFIED
// Property: A user cannot double claim his rewards in claimAllRewards function
rule no_double_claim_in_claimAllRewards(address asset,address to) {
    env e;
    address[] assets = [asset];
    address[] availableRewards = getRewardsByAsset(asset);
    address[] rewardList = getRewardsList();

    // requireInvariant totalSupply_eq_sumAllBalanceAToken();
    require getAvailableRewardsCount(asset) == 1;
    require getRewardsListLength() == 1;
    require availableRewards[0] == rewardList[0];

    claimAllRewards(e,assets,to);

    address[] rewardListOuput;
    uint256[] claimedAmounts;
    rewardListOuput,claimedAmounts = claimAllRewards(e,assets,to);

    assert claimedAmounts[0] == 0 ,
        "user should get zero rewards when claiming second time";

}


// STATUS: TIMEOUT
// Property: A user cannot double claim his rewards in claimRewards function
rule no_double_claim_in_claimRewards(address asset,address to) {
    env e;
    address[] assets = [asset];
    address[] availableRewards = getRewardsByAsset(asset);
    address[] rewardList = getRewardsList();

    require getAvailableRewardsCount(asset) == 1;
    require getRewardsListLength() == 1;
    require availableRewards[0] == rewardList[0];
    
    uint256 amount = getUserRewards(e,assets,e.msg.sender,availableRewards[0]);
    claimRewards(e,assets,amount,to,rewardList[0]);

    uint256 claimedAmount = claimRewards(e,assets,amount,to,availableRewards[0]);

    assert claimedAmount == 0,
        "Double claim should not be possible";
}
