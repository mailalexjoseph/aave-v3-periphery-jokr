import "./ERC20_methods.spec";

using DummyERC20_AToken as AToken;
using DummyERC20_rewardToken as Reward;


/////////////////// Methods ////////////////////////

    methods {
        // 
        function getAssetRewardIndex(address, address) external returns (uint256) envfree;
        function getRewardsData(address, address) external returns (uint256, uint256, uint256, uint256) envfree;
        function getUserAssetIndex(address, address, address) external returns (uint256) envfree;
        function getlastUpdateTimestamp(address asset, address reward) external returns (uint256)  envfree;
        function getDistributionEnd(address asset, address reward) external returns (uint256) envfree;
        function getDistributionEnd(address asset, address reward) external returns (uint256) envfree;
        function getUserAccruedRewards(address user,address asset, address reward) external returns(uint256) envfree;
        function getNthRewardByAsset(address asset,uint8 n) external returns (address) envfree;
        function getAvailableRewardsCount(address asset) external returns (uint256) envfree;
        function getRewardsByAsset(address asset) external returns(address[]) envfree;
        function getCurrentRewardIndex(address asset,address reward) external returns (uint256) envfree;
        function getAssetDecimals(address asset) external returns (uint8) envfree;
        function getUserAccruedRewardsForAsset(address user,address asset, address reward) external returns (uint256) envfree;
        function getRewards(address user, address asset,address reward,uint256 userBalance,uint256 newAssetIndex) external returns(uint256) envfree;
        function getTransferStrategy(address reward) external returns (address) envfree;
        function getRewardOracle(address reward) external returns (address) envfree;
        function getEmissionPerSecond(address asset, address reward) external  returns(uint256) envfree;
        function getEmissionManager() external  returns (address) envfree;
        function getRewardsList() external returns(address[] memory) envfree;
        function getRewardsListLength() external returns(uint256) envfree;
        function getAssetsList() external returns (address[] memory) envfree;
        function getAssetsListLength() external returns (uint256) envfree;
        function getRewardOracle(address) external returns(address) envfree;
        function isContract(address) external returns (bool) envfree;
        function getLatestAnswer(address) external returns (int256) envfree;
        function isRewardEnabled(address reward) external returns(bool) envfree;
        function getRewardsByAssetCount(address asset) external returns(uint256) envfree;
        function getRewardBalance(address,address) external returns (uint256) envfree;
        function getUserAssetBalance(address[], address) external returns (uint256) envfree;
        function getAssetDecimals(address) external returns(uint8) envfree;
        function getScaledTotalSupply(address) external returns(uint256) envfree;
      
         
        // AToken functions
        function _.getScaledUserBalanceAndSupply(address) external => DISPATCHER(true);
        function _.scaledTotalSupply() external => DISPATCHER(true);
        function _.handleAction(address, uint256, uint256) external => DISPATCHER(true);
        function AToken.totalSupply() external returns(uint256) envfree;

        // TransferStrategyBase functions
        function _.performTransfer(address, address, uint256) external => DISPATCHER(true);

        // Oracle - assume any value 
        function _.latestAnswer() external => CONSTANT;

        //envfree functions
        function getUserAccruedRewards(address, address ) external returns(uint256) envfree; 
        function getClaimer(address) external returns (address) envfree;
        function getlastUpdateTimestamp(address asset, address reward) external  returns (uint256) envfree;
        function getAssetDecimals(address asset) external returns (uint8) envfree;
    }



/**************************************************
*                 DEFINITIONS                     *
**************************************************/
definition isConfigureAssets(method f) returns bool = 
    f.selector == sig:configureAssets(RewardsDataTypes.RewardsConfigInput[]).selector;

definition isConfigureAssetsSingle(method f) returns bool =
    f.selector == sig:configureAssetsSingle(RewardsDataTypes.RewardsConfigInput).selector;

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

definition isHarnessMethod(method f) returns bool = 
   isConfigureAssetsHarness(f) || isConfigureAssetsSingle(f);
 
definition claimMethods(method f) returns bool =
    isClaimRewards(f)    || isClaimRewardsOnBehalf(f)    || isClaimRewardsToSelf(f) ||
    isClaimAllRewards(f) || isClaimAllRewardsOnBehalf(f) || isClaimAllRewardsToSelf(f);



////////////////// FUNCTIONS //////////////////////



ghost sumAllBalanceAToken() returns mathint {
   init_state axiom sumAllBalanceAToken() == 0;
}

hook Sstore AToken._userState[KEY address a].balance uint128 balance (uint128 old_balance) STORAGE {
   havoc sumAllBalanceAToken assuming sumAllBalanceAToken@new() == sumAllBalanceAToken@old() + balance - old_balance;
}

hook Sload uint128 val AToken._userState[KEY address a].balance STORAGE {
   require sumAllBalanceAToken() >= to_mathint(val);
}


///////////////// INVARIANTS //////////////////////

invariant totalSupply_eq_sumAllBalanceAToken()
   to_mathint(AToken.totalSupply()) == sumAllBalanceAToken();




