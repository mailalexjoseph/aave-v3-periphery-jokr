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

         
        // AToken functions
        function _.getScaledUserBalanceAndSupply(address) external => DISPATCHER(true);
        function _.scaledTotalSupply() external => DISPATCHER(true);
        function _.handleAction(address, uint256, uint256) external => DISPATCHER(true);
        function AToken.totalSupply() external returns(uint256) envfree;

        // TransferStrategyBase functions
        function _.performTransfer(address, address, uint256) external => DISPATCHER(true);

        // Oracle - assume any value 
        function _.latestAnswer() external => NONDET;

        //envfree functions
        function getUserAccruedRewards(address, address ) external returns(uint256) envfree; 
        function getClaimer(address) external returns (address) envfree;
    }

///////////////// DEFINITIONS //////////////////////

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




