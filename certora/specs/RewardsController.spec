import "methods/Methods_base.spec";


// check this rule for every change in setup to make sure all is reachable 
// use builtin rule sanity;

// Reward index monotonically increase
rule index_keeps_growing(address asset, address reward) {
    uint256 _index = getAssetRewardIndex(asset, reward);

    method f; env e; calldataarg args;
    f(e, args);

    uint256 index_ = getAssetRewardIndex(asset, reward);
    
    assert index_ >= _index;
}

// User index cannot surpass reward index
invariant user_index_LEQ_index(address asset, address reward, address user)
    getUserAssetIndex(user, asset, reward) <= getAssetRewardIndex(asset, reward);


/* 
    Property: claiming reward twice is equivalent to one claim reward 

    Note : this rule is implemented by comparing the whole storage 

*/


rule noDoubleClaim() {

    env e; 
    //arbitrary array of any length (might be constrained due to loop unrolling )
    address[] assets; 
    uint256 l = assets.length;
    address to;
    claimAllRewards(e, assets, to);
    storage afterFirst = lastStorage;
    claimAllRewards(e, assets, to);
    storage afterSecond = lastStorage;

    assert afterSecond == afterFirst;
}

rule onlyAuthorizeCanDecrease(method f) {

    address user; address reward;
    uint256 before = getUserAccruedRewards(user, reward);

    env e;
    calldataarg args;
    f(e,args);

    uint256 after = getUserAccruedRewards(user, reward);

    assert after < before => getClaimer(user) == e.msg.sender; 
}


