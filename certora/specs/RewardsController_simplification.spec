import "methods/Methods_base.spec";


/*
shows one approach of simplifying the rule for dealing with timeouts.
monotonicityOverTime - times out (and is not quite correct as we see in the modular part)
monotonicityOverTime_simpleStart  - is verified 

https://prover.certora.com/output/40726/4ffb9145aa9c4c06ab16808793b51878/?anonymousKey=5705c220c2716e63d395bc238827e7e9e030dd0b 

*/


// this times out 
rule monotonicityOverTime(address user, address reward) {
    
    env e1; 
    env e2;
    address[] assets;
    require (e1.block.timestamp < e2.block.timestamp);
    
    
    assert getUserRewards(e1, assets, user, reward) <=  getUserRewards(e2, assets, user, reward);
}


//just one asset
rule monotonicityOverTimeOneAsset(address user, address reward) {
    
    env e1; 
    env e2;
    address[] assets;
    require (e1.block.timestamp < e2.block.timestamp);
    
    require getlastUpdateTimestamp(assets[0],reward) <= e1.block.timestamp;
    require ( assets.length  == 1);
    assert getUserRewards(e1, assets, user, reward) <=  getUserRewards(e2, assets, user, reward);
}

//same rule but under some more simplification 
function simplify_start(env e, address asset, address reward) {
    require getAssetDecimals(asset) == 6; 
    require getlastUpdateTimestamp(asset,reward) == e.block.timestamp;
}
rule monotonicityOverTime_simpleStart(address user, address reward) {
    
    env e1; 
    env e2;
    address[] assets;
    require (e1.block.timestamp < e2.block.timestamp);
    require ( assets.length  <= 1);
    simplify_start(e1, assets[0], reward);
    
    assert getUserRewards(e1, assets, user, reward) <=  getUserRewards(e2, assets, user, reward);

}
