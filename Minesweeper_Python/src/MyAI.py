# ==============================CS-171==================================
# FILE:			MyAI.py
#
# AUTHOR: 		bugMaker
#
# DESCRIPTION:	This file contains the MyAI class. You will implement your
#				agent in this file. You will write the 'getAction' function,
#				the constructor, and any additional helper functions.
#
# NOTES: 		- MyAI inherits from the abstract AI class in AI.py.
#
#				- DO NOT MAKE CHANGES TO= THIS FILE.
# # ==============================CS-171=================================
from itertools import combinations

from AI import AI
from Action import Action
from collections import defaultdict
import time


class MyAI(AI):
    class Board:
        def __init__(self, rowDimension, colDimension):
            self.board = [['.' for i in range(colDimension)] for j in range(rowDimension)]
            self.__rowDimension = rowDimension
            self.__colDimension = colDimension

        def isValid(self, coor):
            return 0 <= coor[1] < self.__rowDimension and 0 <= coor[0] < self.__colDimension

        def set(self, coor, number):
            if self.isValid(coor):
                self.board[coor[1]][coor[0]] = number

        def get(self, coor):
            if self.isValid(coor):
                return self.board[coor[1]][coor[0]]

    count = 1

    def __init__(self, rowDimension, colDimension, totalMines, startX, startY):

        self.__rowDimension = rowDimension
        self.__colDimension = colDimension
        self.__moveCount = 0
        self.__totalMines = totalMines
        self.__coveredTiles = rowDimension * colDimension
        self.lastCoordinate = (startX, startY)
        self.board = self.Board(rowDimension, colDimension)
        self.safePoints = set()
        self.frontier = set()
        self.searchingPoints = dict()
        self.bombs = set()
        # self.partialCoveredFrontier = []
        # self.partialUncoveredFrontier = []
        # self.potentialBombs = []  # For model checking
        # self.appliedBombs = []  # For model checking
        # self.triedPointsStack = []  # For model checking
        # self.partialUncoveredFrontierCopy = []

        self.triggered = False
        self.cluster = {}

        print("Start New Agent in " + str(MyAI.count))
        MyAI.count += 1

    def hasWon(self) -> bool:
        return self.__coveredTiles - 1 == self.__totalMines

    def flag(self, l: list):
        '''add bombs into self.bombs from a list'''
        for i in l:
            self.bombs.add(i)

    def surroundPoints(self, coordinate) -> list:
        """
            returns 8 surround points (tuples) of a coordinate
        """
        surround_points = []
        for dx in range(-1, 2):
            for dy in range(-1, 2):
                if not (dx == 0 and dy == 0) and self.board.isValid((coordinate[0] + dx, coordinate[1] + dy)):
                    surround_points.append((coordinate[0] + dx, coordinate[1] + dy))
        return surround_points

    def countCovered(self, coordinate: (int, int)) -> int:
        count = 0
        for i in self.surroundPoints(coordinate):
            if self.board.get(i) == '.':
                count += 1
        return count

    def getCovered(self, coordinate) -> list:
        return [i for i in self.surroundPoints(coordinate) if self.board.get(i) == '.' and i not in self.bombs]

    def getUncovered(self, coordinate) -> list:
        return [i for i in self.surroundPoints(coordinate) if self.board.get(i) != '.']

    def countUncovered(self, coordinate) -> list:
        count = 0
        for i in self.surroundPoints(coordinate):
            if self.board.get(i) != '.':
                count += 1
        return count

    def countBombs(self, coordinate: (int, int)) -> int:
        count = 0
        for i in self.surroundPoints(coordinate):
            if i in self.bombs:
                count += 1
        return count

    def deleteFrontier(self):
        ''' eliminate unneeded uncovered frontiers (bombs)'''
        for i in self.bombs:
            if i in self.frontier:
                self.frontier.remove(i)

    def deleteSearchingPoints(self):
        for point in [i for i in self.searchingPoints.keys() if self.countCovered(i) - self.countBombs(i) == 0]:
            del self.searchingPoints[point]

    def uncover(self):
        poping_point = self.safePoints.pop()
        self.lastCoordinate = poping_point
        self.__coveredTiles -= 1
        if poping_point in self.frontier:
            self.frontier.remove(poping_point)
        return Action(AI.Action.UNCOVER, poping_point[0], poping_point[1])

    # CSP methods
    def findNext(self, pointDict):
        # Use euclidean distance to find the next variable
        # Ideas are from stackOverflow
        point = None
        num = -1
        dist = 2800
        for i in pointDict:
            surroundNum = len(
                [x for x in self.surroundPoints(i) if self.board.get(x) != '.' and self.board.get(x) != 0])
            minDist = min(abs(x[0] - i[0]) ** 2 + abs(x[1] - i[1]) ** 2 for x in pointDict if pointDict[x] != 0)

            if pointDict[i] == None and minDist < dist:
                point = i
                num = surroundNum
                dist = minDist
            elif pointDict[i] == None and minDist == dist and surroundNum > num:
                point = i
                num = surroundNum
                dist = minDist
        return point

    def backtrack(self, pointDict: dict, domain: set, output: list, constraint: 'function') -> bool:
        # TO DO: time constraint here
        if time.perf_counter() - self.time > 250:
            return False
        # check finish state
        finish = True
        for i in pointDict.values():
            if i is None:
                finish = False
                break
        if finish == True:
            output.append(pointDict)
            return True
        # select point
        point = self.findNext(pointDict)

        # backtracking the point in both cases (safe or bomb)
        for status in domain:  # domain is {0, 1}, 1 stands for bomb
            pointDict[point] = status

            # check if it satisfy the constraints
            if constraint(pointDict):
                result = self.backtrack(pointDict.copy(), domain, output, constraint)
                # remove assignment
                pointDict[point] = None

                if result == False:
                    return False

    def constraint(self, frontier):
        def build(pointDict) -> bool:
            for point in frontier:
                if not self.checkConstraint(pointDict, point):
                    return False
            return True

        return build

    def checkConstraint(self, pointDict, point):
        current = []

        for i in self.surroundPoints(point):
            if i in self.bombs:
                current.append(1)
            elif self.board.get(i) == '.':
                current.append(pointDict[i])
        if None in current:
            return current.count(1) <= self.board.get(point)

        elif current.count(1) == self.board.get(point):
            return True
        return False

    def cspSetUp(self, uncoveredFrontiers, pointDict):
        constraint = self.constraint(uncoveredFrontiers)
        output = []
        configurationResult = defaultdict(int)
        backtrackResult = self.backtrack(pointDict, {0, 1}, output, constraint)
        if backtrackResult == False and len(self.safePoints) == 0:
            self.randomChoose()

        for i in output:
            for point in i:
                configurationResult[point] += i[point]

        canFindWithoutProbability = False
        for point in configurationResult:
            if configurationResult[point] == 0:
                self.safePoints.add(point)
                canFindWithoutProbability = True
            elif configurationResult[point] == len(output):
                self.bombs.add(point)
                canFindWithoutProbability = True
        if canFindWithoutProbability:
            return configurationResult

        for point in configurationResult:
            # calculate the probability
            configurationResult[point] = configurationResult[point] / len(output)
            self.triggered = True
        return configurationResult

    def randomChoose(self):
        for y in range(self.__rowDimension):
            for x in range(self.__colDimension):
                if self.board.get((x, y)) == '.' and (x, y) not in self.frontier and (x, y) not in self.bombs:
                    self.safePoints.add((x, y))
                    break

    def findRoot(self, point):
        while self.cluster[point] != point:
            point = self.cluster[point]

        return point

    def grouping(self, pivot: (int, int), other: (int, int)):
        if pivot not in self.cluster:
            self.cluster[pivot] = pivot
        if other not in self.cluster:
            self.cluster[other] = other

        self.cluster[self.findRoot(pivot)] = self.findRoot(other)

    def showCluster(self):
        output = defaultdict(set)
        for i in self.cluster:
            output[self.findRoot(i)].add(i)
            output[self.findRoot(i)].add(self.findRoot(i))
        return output.values()

    def getFrontier(self) -> (set, dict):  # revised version
        self.cluster = {}
        for point in self.searchingPoints.keys():
            coveredFrontiers = []
            for i in self.getCovered(point):
                coveredFrontiers.append(i)
            pivot = coveredFrontiers[0]
            for i in coveredFrontiers:
                self.grouping(pivot, i)

        result = []
        for points in self.showCluster():
            uncoveredFrontiers = set()
            for i in points:
                for p in self.getUncovered(i):
                    if self.board.get(p) > 0:
                        uncoveredFrontiers.add(p)
            pointDict = {i: None for i in points}
            result.append((uncoveredFrontiers, pointDict))
        return result

    def getAction(self, number: int) -> "Action Object":
        # preprocessing begins, it only handles easiest cases (rules of thumbs)
        self.board.set(self.lastCoordinate, number)
        if not self.hasWon():
            surround_points = self.surroundPoints(self.lastCoordinate)

            if number == 0:
                for i in surround_points:
                    if self.board.get(i) == '.':
                        self.safePoints.add(i)

            if number != 0:
                self.searchingPoints[self.lastCoordinate] = number
                for i in surround_points:
                    if self.board.get(i) == '.' and i not in self.safePoints:
                        self.frontier.add(i)

            for point in self.searchingPoints.keys():
                surround = self.getCovered(point)
                surroundNum = len(self.surroundPoints(point))
                count = self.countUncovered(point)

                if count == surroundNum - self.searchingPoints[point]:
                    self.flag(surround)  # find the bombs

                if self.searchingPoints[point] == self.countBombs(point):
                    for i in surround:
                        if i not in self.bombs and self.board.get(i) == '.':
                            self.safePoints.add(i)
            # eliminate unneeded uncovered frontiers (bombs)
            self.deleteFrontier()
            # eliminate unneeded covered frontiers
            self.deleteSearchingPoints()
            # add secure uncovered tiles to safe points
            for i in self.frontier:
                if i not in self.bombs and self.board.get(i) == '.' and len(self.bombs) == self.__totalMines:
                    self.safePoints.add(i)

            if len(self.safePoints) > 0:
                return self.uncover()
        # First layer ends here
        # print(f'searchingPoints: {self.searchingPoints.keys()}')
        # print(f'frontier: {self.frontier}')
        # print(f'bombs: {self.bombs}')
        # Second layer
        if not self.hasWon():
            for coveredPoint in self.frontier:
                satisfiable = True
                self.bombs.add(coveredPoint)        #TO DO: logic here got problems!!!
                # print(coveredPoint)
                for uncoveredPoint in self.searchingPoints.keys():
                    if self.searchingPoints[uncoveredPoint] - self.countBombs(uncoveredPoint) != 0:
                        satisfiable = False
                        if len(self.bombs) == self.__totalMines:  # we could find all mines that we could by now, but we can't
                            self.safePoints.add(coveredPoint)  # determine safe points unless there's no mines left
                if not satisfiable:
                    # print(f'removed {coveredPoint}')
                    self.bombs.remove(coveredPoint)

            self.deleteFrontier()
            self.deleteSearchingPoints()
            if len(self.safePoints) > 0:
                return self.uncover()
            # Start find frontier

            '''
            if self.getFrontiers():
                self.doModelChecking()
            # End find frontier
            '''
            # csp begin
            # try:
        if not self.hasWon():
            self.time = time.perf_counter()
            result = {}
            for uncoveredFrontiers, pointDict in sorted(self.getFrontier(), key=lambda x: len(x[1])):
                # print(f'uncovered: {uncoveredFrontiers}')
                # print(f'pointDict: {pointDict}')
                # print(f'searching points: {self.searchingPoints.keys()}')
                cspResult = self.cspSetUp(uncoveredFrontiers, pointDict)
                if self.triggered:
                    result.update(cspResult)

            # except KeyError as e:
            #     self.randomChoose()
            #     print(e)

            self.deleteFrontier()
            self.deleteSearchingPoints()
            #print('csp model checking')
            #print(self.bombs)
            if len(self.safePoints) > 0:
                return self.uncover()

            # probability
            if len(result) != 0:
                min = 1
                chosenPoint = None
                for point, prob in result.items():
                    if prob < min:
                        min = prob
                        chosenPoint = point
                randomProb = (self.__totalMines - len(self.bombs)) / self.__coveredTiles
                if min <= randomProb:
                    self.safePoints.add(chosenPoint)
                else:
                    self.randomChoose()
                self.deleteFrontier()
                self.deleteSearchingPoints()
                #print('probability')
                if len(self.safePoints) > 0:
                    return self.uncover()

            # totally random
            if len(self.safePoints) == 0:
                #print('random')
                self.randomChoose()

            if len(self.safePoints) > 0:
                return self.uncover()

        # Second layer ends here
        # print(self.bombs)
        return Action(AI.Action.LEAVE)

    # def getFrontiers(self):  # False means did that failed, no new value add to frontier True is ...
    #     self.partialUncoveredFrontier = []
    #     self.partialCoveredFrontier = []
    #     if len(self.searchingPoints) == 0:
    #         return False
    #     #'''
    #     for i in self.searchingPoints.keys():
    #         if i not in self.partialUncoveredFrontierCopy:
    #             self.partialUncoveredFrontier.append(i)
    #             break
    #     #'''
    #     #self.partialUncoveredFrontier.append(list(self.searchingPoints.keys())[0])
    #     IsNewValueAdded = True
    #     while IsNewValueAdded:
    #         countUncovered = len(self.partialUncoveredFrontier)
    #         countCovered = len(self.partialCoveredFrontier)
    #         for i in self.partialUncoveredFrontier:
    #             # add covered tiles surrounding by i
    #             if self.countCovered(i) > 0:
    #                 for j in self.getCovered(i):
    #                     if j not in self.partialCoveredFrontier:
    #                         self.partialCoveredFrontier.append(j)
    #
    #         for i in self.partialCoveredFrontier:
    #             # add uncovered tiles surrounding by i
    #             if self.countUncovered(i) > 0:
    #                 for j in self.getUncovered(i):
    #                     if j not in self.partialUncoveredFrontier and j in self.searchingPoints:
    #                         self.partialUncoveredFrontier.append(j)
    #         if len(self.partialUncoveredFrontier) == countUncovered and len(self.partialCoveredFrontier) == countCovered:
    #             IsNewValueAdded = False
    #     self.partialUncoveredFrontierCopy = self.partialUncoveredFrontier.copy()
    #     return True
    #
    # def doModelChecking(self):
    #     if time.perf_counter() - self.time > 5:
    #         return False
    #     if len(self.partialUncoveredFrontierCopy) == 0:
    #         return False
    #     checkPoint = self.partialUncoveredFrontierCopy.pop(0)
    #     if self.searchingPoints[checkPoint] - self.countBombs(checkPoint) < 0:
    #         return False
    #     potentialBombs = (checkPoint, [i for i in combinations(self.getCovered(checkPoint), self.searchingPoints[checkPoint] - self.countBombs(checkPoint))])
    #     potentialBombs[1].append((-1, -1))
    #
    #     if len(self.partialUncoveredFrontierCopy) == 0:
    #         for bombs in potentialBombs[1]:
    #             self.appliedBombs.append([])
    #             if bombs == (-1, -1):
    #                 if self.isValid():
    #                     return True
    #                 else:
    #                     self.appliedBombs.pop(-1)
    #             else:
    #                 for bomb in bombs:
    #                     if bomb not in self.bombs:
    #                         self.appliedBombs[-1].append(bomb)
    #                         self.bombs.add(bomb)
    #                 if self.isValid():
    #                     return True
    #                 else:
    #                     for i in self.appliedBombs[-1]:
    #                         self.bombs.discard(i)
    #                     self.appliedBombs.pop(-1)
    #         self.partialUncoveredFrontierCopy.insert(0, checkPoint)
    #         return False
    #
    #     for bombs in potentialBombs[1]:
    #         self.appliedBombs.append([])
    #         if bombs == (-1, -1):
    #             if self.doModelChecking():
    #                 return True
    #             else:
    #                 self.appliedBombs.pop(-1)
    #                 break
    #         for bomb in bombs:
    #             if bomb in self.bombs:
    #                 pass
    #             else:
    #                 self.appliedBombs[-1].append(bomb)
    #                 self.bombs.add(bomb)
    #         if self.doModelChecking():
    #             return True
    #         for i in self.appliedBombs[-1]:
    #             self.bombs.discard(i)
    #         self.appliedBombs.pop(-1)
    #     self.partialUncoveredFrontierCopy.insert(0, checkPoint)
    #     return False
    #
    #
    # def isValid(self):
    #     for i in self.partialUncoveredFrontier:
    #         if self.searchingPoints[i] != self.countBombs(i):
    #             return False
    #     for j in self.partialCoveredFrontier:
    #         if j not in self.bombs:
    #             self.safePoints.add(j)
    #     return True
