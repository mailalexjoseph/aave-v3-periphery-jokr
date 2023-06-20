import "methods/Methods_base.spec";

// index mono increase
rule index_keeps_growing(address asset, address reward) {
    uint256 _index = getAssetRewardIndex(asset, reward);

    method f; env e; calldataarg args;
    f(e, args);

    uint256 index_ = getAssetRewardIndex(asset, reward);
    
    assert index_ >= _index;
}


invariant user_index_LEQ_index(address asset, address reward, address user)
    getUserAssetIndex(user, asset, reward) <= getAssetRewardIndex(asset, reward);

