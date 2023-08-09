import "methods/Methods_base.spec";
import "RewardsController_base.spec";
using TransferStrategyHarness as TransferStrategy;
use invariant totalSupply_eq_sumAllBalanceAToken;
use invariant user_index_LEQ_index;
use rule index_keeps_growing;
use rule onlyAuthorizeCanDecrease;

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


invariant user_rewards_LEQ_emissions_till_now(env e, address user, address asset, address reward)
    getAllUserRewards(e,user,asset,reward) <= currentAvailableRewards(e,asset,reward)
    {
        preserved {
            requireInvariant totalSupply_eq_sumAllBalanceAToken();
            require getlastUpdateTimestamp(asset,reward) == e.block.timestamp;
            require getAssetDecimals(asset) == 6;
        }
        preserved handleAction(address user1,uint256 totalSupply,uint256 userBalance) with(env e1) {
            require e1.block.timestamp == e.block.timestamp;
            uint256 userBalance1; uint256 totalSupply1;
            userBalance1,totalSupply1 = AToken.getScaledUserBalanceAndSupply(e,user1);
            require totalSupply == totalSupply1 && userBalance == userBalance1;
        }
    }


// STATUS: VIOLATED
// https://prover.certora.com/output/547/16a9617240b84441896f713804f693fd/?anonymousKey=c29e8aceada83507965dbe11d428a4af5814bffe
// invariant user_owns_rewards_LEQ_emissions_till_now(env e, address user, address asset, address reward)
//     Reward.balanceOf(e,user) <= currentAvailableRewards(e,asset,reward)
//     {
//          preserved {
//             requireInvariant totalSupply_eq_sumAllBalanceAToken();
//             require getAssetDecimals(asset) == 6;
//             require getlastUpdateTimestamp(asset,reward) == e.block.timestamp;
//         }
//         preserved handleAction(address user1,uint256 totalSupply,uint256 userBalance) with(env e1) {
//             require e1.block.timestamp == e.block.timestamp;
//             uint256 userBalance1; uint256 totalSupply1;
//             userBalance1,totalSupply1 = AToken.getScaledUserBalanceAndSupply(e,user1);
//             require totalSupply == totalSupply1 && userBalance == userBalance1;
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

// STAUS: VERIFIED
rule configureAssets_updates_asset_list (env e, RewardsDataTypes.RewardsConfigInput rewardInput) {
    require getAssetsListLength() == 0;
    uint8 assetDecimals = getAssetDecimals(rewardInput.asset);

    configureAssetsSingle(e, rewardInput);

    address[] assetList = getAssetsList(); 
    uint256 length = getAssetsListLength();

    assert assetDecimals == 0 <=> length == 1 && assetList[0] == rewardInput.asset;
}

// STAUS: VERIFIED
rule configureAssets_updates_reward_list (env e, RewardsDataTypes.RewardsConfigInput rewardInput) {
    require getRewardsListLength() == 0;
    bool enabledBefore = isRewardEnabled(rewardInput.reward);

    configureAssetsSingle(e, rewardInput);

    address[] rewardList = getRewardsList(); 
    uint256 length = getRewardsListLength();
    bool enabledAfter = isRewardEnabled(rewardInput.reward);

    assert enabledBefore == false <=> length == 1 && rewardList[0] == rewardInput.reward;
    assert enabledAfter == true;

}

// STAUS: VERIFIED
rule configureAssets_updates_available_rewards (env e, RewardsDataTypes.RewardsConfigInput rewardInput) {
    require getAvailableRewardsCount(rewardInput.asset) == 0;
    uint256 lastUpdateTimestamp = getlastUpdateTimestamp(rewardInput.asset, rewardInput.reward);
    
    configureAssetsSingle(e, rewardInput);

    address[] availableRewards = getRewardsByAsset(rewardInput.asset); 
    uint256 length = getAvailableRewardsCount(rewardInput.asset);

    assert lastUpdateTimestamp == 0 <=> length == 1 && availableRewards[0] == rewardInput.reward;
}

// STATUS: VERIFIED
rule claimAllRewards_unit_test(address asset,address to) {
    env e;
    address[] assets = [asset];

    address[] availableRewards = getRewardsByAsset(asset);
    require getAvailableRewardsCount(asset) == 1;

    address[] rewardList = getRewardsList();
    require getRewardsListLength() == 1;

    address reward = rewardList[0];

    require availableRewards[0] == rewardList[0];
    require getAvailableRewardsCount(asset) == 1;
    

    uint256 rewards = getUserRewards(e,assets,e.msg.sender,reward);

    address[] rewardListOutput ; uint256[] claimedAmounts;
    rewardListOutput,claimedAmounts = claimAllRewards(e,assets,to);

    uint256 accruedRewards_ = getUserAccruedRewardsForAsset(e.msg.sender,asset,reward);

    assert accruedRewards_ == 0,
        "Accrued rewards must be zero after claiming all rewards"; 
    assert claimedAmounts[0] == rewards,
        "Incorrect claimedAmounts";

}



// STATUS: VERIFIED 
rule claimAllRewards_should_update_index_data(address asset,address to) {
    env e;
    address[] assets = [asset];

    address[] availableRewards = getRewardsByAsset(asset);
    require getAvailableRewardsCount(asset) == 1;

    address[] rewardList = getRewardsList();
    require getRewardsListLength() == 1;

    address reward = rewardList[0];

    require availableRewards[0] == rewardList[0];
    require getAvailableRewardsCount(asset) == 1;
    
    uint256 oldIndex ; uint256 newIndex;
    oldIndex,newIndex = getAssetIndex(e,asset,reward);

    claimAllRewards(e,assets,to);

    assert getCurrentRewardIndex(asset,reward) == newIndex,
        "Incorrect reward index update";
    assert getUserAssetIndex(e.msg.sender,asset,reward) == newIndex,
        "Incorrect user index update";
    assert getlastUpdateTimestamp(asset,reward) == e.block.timestamp,
        "Incorrect lastUpdateTimestamp";
}

// STATUS: VERIFIED
// Property: ClaimAllRewards should increase the rewards balance of user
rule claimAllRewards_should_increase_reward_balance(address asset,address to) {
    env e;
    address[] assets = [asset];

    address[] availableRewards = getRewardsByAsset(asset);
    require getAvailableRewardsCount(asset) == 1;

    address[] rewardList = getRewardsList();
    require getRewardsListLength() == 1;

    address reward = rewardList[0];

    require availableRewards[0] == rewardList[0];
    require getAvailableRewardsCount(asset) == 1;

    uint256 _balance = Reward.balanceOf(e,to);

    address[] rewardListOutput ; uint256[] claimedAmounts;
    rewardListOutput,claimedAmounts = claimAllRewards(e,assets,to);

    uint256 balance_ = Reward.balanceOf(e,to);

    assert to != TransferStrategy => to_mathint(balance_) == _balance + claimedAmounts[0],
        "user rewards should increase after claimAllRewards";

}

// STATUS: VERIFIED
// Property: setDistributionEnd is behaving as expected
rule setDistributionEnd_unit_test(address asset,address reward,uint32 newDistributionEnd) {
    env e;
    setDistributionEnd(e,asset,reward,newDistributionEnd);

    assert assert_uint32(getDistributionEnd(asset,reward)) == newDistributionEnd,
        "distributionEnd not updated";
    assert e.msg.sender == getEmissionManager(),
        "distribution should only be changed by manager";

}


// Rules - ClaimRewards unit tests
// STATUS: VERIFIED
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

// STATUS: VERIFIED
rule getUserRewards_unit_test (
    env e,
    address asset,
    address user,
    address reward
) {
    address[] assets = [asset];
    require getAssetDecimals(asset) == 8;

    uint256 userBalance = getUserAssetBalance(assets, user);

    uint256 unclaimedRewards = getUserAccruedRewards(user, asset, reward);

    uint256 userIndex = getUserAssetIndex(user, asset, reward);
    uint256 oldIndex; uint256 reserveIndex;
    oldIndex, reserveIndex = getAssetIndex(e, asset, reward);
    mathint result = userBalance * (reserveIndex - userIndex);
    mathint assetUnit = 10^getAssetDecimals(asset);
    mathint pendingRewards = result / assetUnit;

    uint256 expectedRewards = getUserRewards(e, assets, user, reward);

    assert userBalance == 0 => expectedRewards == unclaimedRewards;
    assert userBalance != 0 =>  expectedRewards == assert_uint256(unclaimedRewards + pendingRewards);

}

// STATUS: VERIFIED
rule getAssetIndex_uint_test (
    env e,
    address asset,
    address reward
) {
    require getAssetDecimals(asset) == 8;

    uint256 oldIndex; uint256 distributionEnd;  uint256 emissionPerSecond; uint256 lastUpdateTimestamp;
    oldIndex, emissionPerSecond, lastUpdateTimestamp, distributionEnd = getRewardsData(asset, reward);
    mathint totalSupply = getScaledTotalSupply(asset);
    mathint assetUnit = 10^getAssetDecimals(asset);
    uint256 currentTimeStamp;

    if (e.block.timestamp > distributionEnd){
        currentTimeStamp = distributionEnd;
    }
    else {
        currentTimeStamp = e.block.timestamp;
    }
    
    mathint timeDelta = currentTimeStamp - lastUpdateTimestamp;
    mathint firstTerm = emissionPerSecond * timeDelta * assetUnit;

    mathint computedNewIndex;
    if (totalSupply == 0){
        computedNewIndex = oldIndex;
    }
    else {
        computedNewIndex =  (firstTerm / totalSupply) + oldIndex;
    }
    

    uint256 oldIndexExpected; uint256 newIndexExpected;
    oldIndexExpected, newIndexExpected = getAssetIndex(e, asset, reward);

    assert (
        emissionPerSecond == 0 ||
        totalSupply == 0 ||
        lastUpdateTimestamp == e.block.timestamp ||
        lastUpdateTimestamp >= distributionEnd
    ) => oldIndexExpected == oldIndex && newIndexExpected == oldIndex;

    assert (
        emissionPerSecond != 0 &&
        totalSupply != 0 &&
        lastUpdateTimestamp != e.block.timestamp &&
        lastUpdateTimestamp < distributionEnd
    ) => oldIndexExpected == oldIndex && newIndexExpected == assert_uint256(computedNewIndex);
}


rule setTransferStrategyUnitTest(address reward, address transferStrategy) {
    env e;
    setTransferStrategy(e,reward, transferStrategy);
    assert getTransferStrategy(reward) == transferStrategy;
    assert e.msg.sender == getEmissionManager();
}

rule setRewardOracleUnitTest(address reward, address rewardOracle) {
    env e;
    setRewardOracle(e,reward, rewardOracle);
    assert getRewardOracle(reward) == rewardOracle;
    assert e.msg.sender == getEmissionManager();
}

rule setClaimerUnitTest(address user, address caller) {
    env e;
    setClaimer(e,user, caller);
    assert getClaimer(e,user) == caller;
    assert e.msg.sender == getEmissionManager();
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
    env e;
    setTransferStrategy@withrevert(e,reward, transferStrategy);
    bool setTransferStrategyReverted = lastReverted;
    assert transferStrategy == 0 || !isContract(transferStrategy) => setTransferStrategyReverted,
        "transferStrategy should never be zero address";        
}

rule setRewardOracle_should_revert(address reward, address rewardOracle) {
    env e;  
    setRewardOracle@withrevert(e,reward, rewardOracle);
    bool setRewardOracleReverted = lastReverted;
    assert getLatestAnswer(rewardOracle) <= 0 => setRewardOracleReverted,
        "oracle must return price";
}

rule transferRewards_should_revert(address to, address reward, uint256 amount) {
    env e;
    address transferStrategy = getTransferStrategy(reward);
    require transferStrategy != to;

    uint256 balanceBefore = Reward.balanceOf(e, to);
    transferRewards@withrevert(e, to, reward, amount);
    bool transferRewardsReverted = lastReverted;
    uint256 balanceAfter = Reward.balanceOf(e, to);

    assert amount != 0 && balanceAfter == balanceBefore <=> transferRewardsReverted,
        "transfer should revert on failure";
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
rule only_claim_functions_can_decrease_accrued_rewards(address user,address reward,method f) filtered { f -> !f.isView && !isHarnessMethod(f)} {
    
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


// STATUS: VERIFIED
// Property: computeNewIndexChange should returns zero if lastupdateTimestamp is current timestamp
rule index_change_should_be_zero(){
    env e;
    uint256 totalSupply; uint256 block_timestamp; 
    uint256 lastUpdateTimestamp; uint256 distributionEnd;
    uint256 emissionPerSecond; uint256 assetUnit;
    

    uint256 change = computeNewIndexChange(e,totalSupply,block_timestamp,lastUpdateTimestamp,distributionEnd,emissionPerSecond,assetUnit);

    assert block_timestamp == lastUpdateTimestamp => change == 0,
        "index change should be zero if last change is current block";
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
rule no_double_claim_in_claimRewards(address[] assets,address to) {
    env e;

    address asset = assets[0];
    address[] availableRewards = getRewardsByAsset(asset);
    address[] rewardList = getRewardsList();

    require assets.length == 1;
    require getAssetsListLength() == 2;
    require getRewardsListLength() == 1;
    require getAvailableRewardsCount(asset) == 1;


    require getAvailableRewardsCount(asset) == 1;
    require getRewardsListLength() == 1;
    require availableRewards[0] == rewardList[0];
    
    uint256 amount = getUserRewards(e,assets,e.msg.sender,availableRewards[0]);
    claimRewards(e,assets,amount,to,rewardList[0]);

    uint256 claimedAmount = claimRewards(e,assets,amount,to,availableRewards[0]);

    assert claimedAmount == 0,
        "Double claim should not be possible";
}



// STATUS: VIOLATED
// Property: handleAction should never revert no matter what
// handleAction function got reverted in 2 scernarios:
//      1. When the reward index overflows and 
//      2. 
rule handleAction_should_never_revert(method f) {
    env e;
    address user1;
    uint256 totalSupply1;
    uint256 userBalance1;

    handleAction@withrevert(e,user1,totalSupply1,userBalance1);
    bool firstReverted = lastReverted;
    
    calldataarg args;

    f(e,args);

    address user2;
    uint256 totalSupply2;
    uint256 userBalance2;

    handleAction@withrevert(e,user2,totalSupply2,userBalance2);
    bool secondReverted = lastReverted;

    assert !firstReverted => !secondReverted,
        "handleAction should never revert";
    
}


// STATUS: VERIFIED
// Property: user rewards should never decrease unless claimed
// rule rewards_should_never_decrease_unless_claimed(){
//     env e;
//     method f;
//     calldataarg args;

//     address asset;
//     require getAssetDecimals(asset) == 6;

//     address[] assets;
//     address user;
//     address reward;

//     uint _rewards = getUserRewards(e,assets,user,reward);
 
//     f(e,args);

//     uint rewards_ = getUserRewards(e,assets,user,reward);

//     assert !claimMethods(f) => rewards_ >= _rewards,
//         "user rewards should not decrease unless claimed";


// }
