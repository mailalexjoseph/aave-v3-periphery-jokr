// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.10;

import {RewardsController} from '../../contracts/rewards/RewardsController.sol';
import {RewardsDataTypes} from '../../contracts/rewards/libraries/RewardsDataTypes.sol';
import {IScaledBalanceToken} from '@aave/core-v3/contracts/interfaces/IScaledBalanceToken.sol';

contract RewardsControllerHarness is RewardsController {
  constructor(address emissionManager) RewardsController(emissionManager) {}

  // returns an asset's reward index
  function getAssetRewardIndex(address asset, address reward) external view returns (uint256) {
    return _assets[asset].rewards[reward].index;
  }

  function getlastUpdateTimestamp(address asset, address reward) external view returns (uint256) {
    return _assets[asset].rewards[reward].lastUpdateTimestamp;
  }

  function getAvailableRewardsCount(address asset) external view returns (uint256) {
    return uint256(_assets[asset].availableRewardsCount);
  }

  function getUserAccruedRewards(
    address user,
    address asset,
    address reward
  ) external view returns (uint256) {
    return _assets[asset].rewards[reward].usersData[user].accrued;
  }

  function getAllUserRewards(
    address user,
    address asset,
    address reward
  ) external view returns (uint256) {
    RewardsDataTypes.UserAssetBalance[]
      memory userAssetBalances = new RewardsDataTypes.UserAssetBalance[](1);
    userAssetBalances[0].asset = asset;
    (userAssetBalances[0].userBalance, userAssetBalances[0].totalSupply) = IScaledBalanceToken(
      asset
    ).getScaledUserBalanceAndSupply(user);

    return
      _assets[asset].rewards[reward].usersData[user].accrued +
      _getPendingRewards(user, reward, userAssetBalances[0]);
  }

  function getNthRewardByAsset(address asset, uint8 n) external view returns (address) {
    require(_assets[asset].availableRewardsCount >= n, 'No rewards');
    return _assets[asset].availableRewards[n - 1];
  }

  function getCurrentRewardIndex(address asset, address reward) external view returns (uint256) {
    RewardsDataTypes.RewardData storage rewardData = _assets[asset].rewards[reward];
    return rewardData.index;
  }

  function getUserAccruedRewardsForAsset(
    address user,
    address asset,
    address reward
  ) external view returns (uint256) {
    return _assets[asset].rewards[reward].usersData[user].accrued;
  }

  function getRewards(
    address user,
    address asset,
    address reward,
    uint256 userBalance,
    uint256 newAssetIndex
  ) external view returns (uint256) {
    uint256 assetUnit = 10 ** _assets[asset].decimals;
    uint256 userIndex = _assets[asset].rewards[reward].usersData[user].index;
    return _getRewards(userBalance, newAssetIndex, userIndex, assetUnit);
  }

  function getEmissionPerSecond(address asset, address reward) external view returns (uint256) {
    return _assets[asset].rewards[reward].emissionPerSecond;
  }

  function configureAssetsHarness(
    RewardsDataTypes.RewardsConfigInput memory rewardInput1,
    RewardsDataTypes.RewardsConfigInput memory rewardInput2
  ) external {
    RewardsDataTypes.RewardsConfigInput[]
      memory rewardsInput = new RewardsDataTypes.RewardsConfigInput[](2);
    rewardsInput[0] = rewardInput1;
    rewardsInput[1] = rewardInput2;
    this.configureAssets(rewardsInput);
  }

  function currentAvailableRewards(address asset, address reward) external view returns (uint256) {
    (, uint256 newIndex) = this.getAssetIndex(asset, reward);
    uint256 assetUnit = 10 ** _assets[asset].decimals;
    uint256 totalSupply = IScaledBalanceToken(asset).scaledTotalSupply();
    return _getRewards(totalSupply, newIndex, 0, assetUnit);
  }

  function getRewardsListLength() external view returns (uint256) {
    return _rewardsList.length;
  }

  function getAssetsList() external view  returns (address[] memory) {
    return _assetsList;
  }

  function getAssetsListLength() external view returns (uint256) {
    return _assetsList.length;
  }
}
